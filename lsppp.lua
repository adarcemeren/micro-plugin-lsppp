-- ============================================================================
-- LSP++ (Micro Editor Plugin)
-- ============================================================================
-- Version: 1.0.0
-- Description: A high-performance, lightweight LSP client for C/C++ in Micro.
--              LSP++ provides seamless auto-completion, intelligent formatting,
--              and real-time diagnostics by interfacing with the clangd server.
--              Engineered for stability, it features dynamic viewport management
--              to prevent UI overflows and robust buffer synchronization.
-- ============================================================================
local micro = import("micro")
local config = import("micro/config")
local buffer = import("micro/buffer")
local shell = import("micro/shell")
local util = import("micro/util")
local fmt = import("fmt")
local go_os = import("os")
local strings = import("strings")

-- ============================================================================
-- 1. JSON PARSER ENGINE
-- ============================================================================
-- Micro's Lua API does not expose a native JSON parser. To enable JSON-RPC
-- communication with the language server, we implement a compliant recursive
-- descent parser here. This handles object nesting and string escaping.
-- ============================================================================

json = {}

-- Helper: Identifies if a table is an array or a key-value object.
local function kind_of(obj)
    if type(obj) ~= 'table' then
        return type(obj)
    end
    local i = 1
    for _ in pairs(obj) do
        if obj[i] ~= nil then
            i = i + 1
        else
            return 'table'
        end
    end
    if i == 1 then
        return 'table'
    else
        return 'array'
    end
end

-- Helper: Advances the parser past delimiters and whitespace.
local function skip_delim(str, pos, delim, err_if_missing)
    pos = pos + #str:match('^%s*', pos)
    if str:sub(pos, pos) ~= delim then
        if err_if_missing then
            error('Expected ' .. delim .. ' near position ' .. pos)
        end
        return pos, false
    end
    return pos + 1, true
end

-- Helper: Parses JSON string literals, resolving escape sequences.
local function parse_str_val(str, pos, val)
    val = val or ''
    local early_end_error = 'End of input found while parsing string.'
    if pos > #str then
        error(early_end_error)
    end
    local c = str:sub(pos, pos)
    if c == '"' then
        return val, pos + 1
    end
    if c ~= '\\' then
        return parse_str_val(str, pos + 1, val .. c)
    end

    local esc_map = {
        b = '\b',
        f = '\f',
        n = '\n',
        r = '\r',
        t = '\t'
    }
    local nextc = str:sub(pos + 1, pos + 1)
    if not nextc then
        error(early_end_error)
    end
    return parse_str_val(str, pos + 2, val .. (esc_map[nextc] or nextc))
end

-- Helper: Parses numeric values (integers, floats, scientific notation).
local function parse_num_val(str, pos)
    local num_str = str:match('^-?%d+%.?%d*[eE]?[+-]?%d*', pos)
    local val = tonumber(num_str)
    if not val then
        error('Error parsing number at position ' .. pos .. '.')
    end
    return val, pos + #num_str
end

json.null = {}

-- Core JSON parsing function.
function json.parse(str, pos, end_delim)
    pos = pos or 1
    if pos > #str then
        error('Reached unexpected end of input.')
    end
    local pos = pos + #str:match('^%s*', pos)
    local first = str:sub(pos, pos)

    if first == '{' then
        local obj, key, delim_found = {}, true, true
        pos = pos + 1
        while true do
            key, pos = json.parse(str, pos, '}')
            if key == nil then
                return obj, pos
            end
            if not delim_found then
                error('Comma missing between object items.')
            end
            pos = skip_delim(str, pos, ':', true)
            obj[key], pos = json.parse(str, pos)
            pos, delim_found = skip_delim(str, pos, ',')
        end
    elseif first == '[' then
        local arr, val, delim_found = {}, true, true
        pos = pos + 1
        while true do
            val, pos = json.parse(str, pos, ']')
            if val == nil then
                return arr, pos
            end
            if not delim_found then
                error('Comma missing between array items.')
            end
            arr[#arr + 1] = val
            pos, delim_found = skip_delim(str, pos, ',')
        end
    elseif first == '"' then
        return parse_str_val(str, pos + 1)
    elseif first == '-' or first:match('%d') then
        return parse_num_val(str, pos)
    elseif first == end_delim then
        return nil, pos + 1
    else
        local literals = {
            ['true'] = true,
            ['false'] = false,
            ['null'] = json.null
        }
        for lit_str, lit_val in pairs(literals) do
            local lit_end = pos + #lit_str - 1
            if str:sub(pos, lit_end) == lit_str then
                return lit_val, lit_end + 1
            end
        end
        error('Invalid json syntax starting at position ' .. pos)
    end
end

-- ============================================================================
-- 2. UI TOOLTIP SYSTEM
-- ============================================================================
-- The Tooltip system creates a floating-like window using Micro's split panes.
-- It strips standard UI elements (rulers, status lines) to mimic a pop-up menu.
-- ============================================================================

-- Transforms buffer logical coordinates (Loc) to screen visual coordinates.
-- Handles soft-wrap offsets to ensure precise positioning relative to the cursor.
local function ScreenLocFromBufLoc(bp, loc)
    local vloc = bp:VLocFromLoc(loc)
    local ix, iy = vloc.VisualX, vloc.Line + vloc.Row
    local bufView = bp:BufView()

    local numExtraLines = 0
    if bp.Buf.Settings["softwrap"] then
        local startLine = bufView.StartLine.Line
        numExtraLines = numExtraLines - bufView.StartLine.Row
        for l = startLine, vloc.Line - 1 do
            local line = bp.Buf:Line(l)
            local lineEndX = util.CharacterCountInString(line)
            local sloc = bp:SLocFromLoc(buffer.Loc(lineEndX, l))
            numExtraLines = numExtraLines + sloc.Row
        end
    end

    return {
        X = bufView.X - bufView.StartCol + ix,
        Y = bufView.Y - bufView.StartLine.Line + numExtraLines + iy
    }
end

local function GetSplitIndex(bp)
    if not bp then
        return 0
    end
    return bp:Tab():GetPane(bp:ID())
end

-- Snapshots current pane layout to restore it after the tooltip closes.
-- This prevents the "destructive" split action from ruining the user's workspace.
local function TabLayoutSnapshot(tab, tooltipIdx)
    local snapshot = {}
    local panes = tab.Panes
    for i = 1, #panes do
        if not tooltipIdx or i ~= tooltipIdx + 1 then
            local paneView = panes[i]:GetView()
            table.insert(snapshot, {
                view = paneView,
                viewValue = -paneView
            })
        end
    end
    return snapshot
end

local function TabLayoutRecover(snapshot)
    for _, pane in ipairs(snapshot) do
        pane.view.X = pane.viewValue.X
        pane.view.Y = pane.viewValue.Y
        pane.view.Width = pane.viewValue.Width
        pane.view.Height = pane.viewValue.Height
        pane.view.StartLine = pane.viewValue.StartLine
        pane.view.StartCol = pane.viewValue.StartCol
    end
end

-- Initializes the scratch buffer for the tooltip.
-- Removes UI decorations like line numbers and status bars.
local function SetTooltipBuffer(data, name)
    local buf = buffer.NewBuffer(data, name)
    buf.Type.Scratch = true
    buf.Type.Readonly = true
    buf:SetOptionNative("ruler", false)
    buf:SetOptionNative("statusline", false)
    -- Clears the status format to remove the separator line artifact (----)
    buf:SetOptionNative("statusformatl", "")
    buf:SetOptionNative("statusformatr", "")
    buf:SetOptionNative("softwrap", false)
    buf:SetOptionNative("scrollbar", false)
    return buf
end

local Tooltip = {}
Tooltip.__index = Tooltip

-- Constructor: Creates the tooltip pane.
function Tooltip.new(name, content, x, y, width, height)
    local self = setmetatable({}, Tooltip)
    self.name = name
    self.origin = micro.CurPane()
    self.bp = nil

    local snapshot = TabLayoutSnapshot(self.origin:Tab(), nil)
    local buf = SetTooltipBuffer(content, name)

    self.origin:HSplitIndex(buf, true)
    self.bp = micro.CurPane()

    -- Add +1 padding to height to prevent last-line clipping.
    self.bp:Resize(width, height + 1)

    local tooltipView = self.bp:GetView()
    tooltipView.X, tooltipView.Y = x, y

    -- Force Reset Viewport: Ensures the list always starts from the top item.
    tooltipView.StartLine.Line = 0
    tooltipView.StartLine.Row = 0

    TabLayoutRecover(snapshot)
    self.origin:Tab():SetActive(GetSplitIndex(self.origin))
    return self
end

-- Updates the tooltip content and geometry without recreating the pane.
function Tooltip:Update(content, x, y, width, height)
    if not self.bp then
        return
    end
    self.bp.Buf:Replace(buffer.Loc(0, 0), self.bp.Buf:End(), content)

    local snapshot = TabLayoutSnapshot(self.origin:Tab(), GetSplitIndex(self.bp))
    self.bp:Resize(width, height + 1)

    local tooltipView = self.bp:GetView()
    tooltipView.X, tooltipView.Y = x, y

    -- Reset Viewport on update to sync with scroll logic.
    tooltipView.StartLine.Line = 0
    tooltipView.StartLine.Row = 0

    TabLayoutRecover(snapshot)
    self.origin:Tab():SetActive(GetSplitIndex(self.origin))
end

function Tooltip:Close()
    if not self.bp then
        return nil
    end
    local snapshot = TabLayoutSnapshot(self.origin:Tab(), GetSplitIndex(self.bp))
    self.bp:Quit()
    self.bp = nil

    local originIdx = GetSplitIndex(self.origin)
    self.origin:Tab():SetActive(originIdx)
    TabLayoutRecover(snapshot)
    return nil
end

-- ============================================================================
-- 3. GLOBAL STATE & CONFIGURATION
-- ============================================================================

cmd = nil -- Subprocess handle for the Language Server
currentAction = {} -- Callback for the pending async request
requestId = 0 -- RPC ID counter
message = '' -- Stream buffer
rootUri = '' -- Project root URI
completionResults = {} -- Autocomplete candidates
selectedIndex = 1 -- Cursor index in completion list
activeTooltip = nil -- Active tooltip instance
isFormatting = false -- Semaphore for formatting operations
version = {} -- File versioning
capabilities = {} -- Server capabilities
scrollOffset = 0 -- Pagination state

function init()
    -- Register Options with 'lsppp' prefix
    config.RegisterCommonOption("lsppp", "autoformat", true)
    config.RegisterCommonOption("lsppp", "autostart", true)
    config.RegisterCommonOption("lsppp", "autocomplete", true)

    -- Register Commands (using 'lsppp' prefix)
    config.MakeCommand("lspppstart", startServer, config.NoComplete)
    config.MakeCommand("lspppstop", stopServer, config.NoComplete)
    config.MakeCommand("lspppformat", formatAction, config.NoComplete)
    config.MakeCommand("lspppdef", definitionAction, config.NoComplete)
    config.MakeCommand("lsppprefs", referencesAction, config.NoComplete)

    -- Core Completion Command
    config.MakeCommand("lspppcomplete", completionAction, config.NoComplete)

    -- Internal Navigation Commands (Bound dynamically)
    config.MakeCommand("lsppp_confirm", function()
        ConfirmCompletion(micro.CurPane())
    end, config.NoComplete)
    config.MakeCommand("lsppp_escape", function()
        CloseTooltip()
    end, config.NoComplete)
    config.MakeCommand("lsppp_backspace", backspaceAction, config.NoComplete)

    -- Default Keybinding
    config.TryBindKey("CtrlSpace", "command:lspppcomplete", true)
end

-- ============================================================================
-- 4. LSP COMMUNICATION LAYER
-- ============================================================================

function getUriFromBuf(buf)
    if buf == nil then
        return
    end
    local file = buf.AbsPath
    local uri = fmt.Sprintf("file://%s", file)
    return uri
end

-- Sends a JSON-RPC message to the server.
function send(method, params, isNotification)
    if cmd == nil then
        return
    end
    local msg = fmt.Sprintf('{"jsonrpc": "2.0", %s"method": "%s", "params": %s}',
        not isNotification and fmt.Sprintf('"id": %.0f, ', requestId) or "", method, params)
    requestId = requestId + 1
    msg = fmt.Sprintf("Content-Length: %.0f\r\n\r\n%s", #msg, msg)
    shell.JobSend(cmd, msg)
end

-- Processes stdout stream, handling fragmentation.
function onStdout(text)
    message = message .. text
    while true do
        local s, e = message:find("Content%-Length: %d+\r\n\r\n")
        if not s then
            return
        end

        local contentLength = tonumber(message:match("Content%-Length: (%d+)", s))
        if #message < e + contentLength then
            return
        end

        local body = message:sub(e + 1, e + contentLength)
        message = message:sub(e + contentLength + 1)

        local status, data = pcall(json.parse, body)
        if status and data then
            if currentAction.method and not data.method and currentAction.response and data.jsonrpc then
                local bp = micro.CurPane()
                currentAction.response(bp, data)
                if currentAction.method ~= "textDocument/completion" then
                    currentAction = {}
                end
            elseif data.method == "textDocument/publishDiagnostics" then
                handleDiagnostics(data.params)
            end
        end
    end
end

function onStderr(text)
end
function onExit(str)
    cmd = nil;
    currentAction = {}
end

-- ============================================================================
-- 5. HELPERS
-- ============================================================================

-- Identifies the word prefix at the cursor for fuzzy filtering.
function getWordPrefix(bp)
    local line = bp.Buf:Line(bp.Cursor.Y)
    local x = bp.Cursor.X
    if x == 0 then
        return ""
    end

    local i = 1
    local count = 0
    while i <= #line and count < x do
        local b = line:byte(i)
        local charLen = 1
        if b >= 240 then
            charLen = 4
        elseif b >= 224 then
            charLen = 3
        elseif b >= 192 then
            charLen = 2
        end
        i = i + charLen
        count = count + 1
    end

    local sub = line:sub(1, i - 1)
    return sub:match("[%w_]+$") or ""
end

-- ============================================================================
-- 6. UI LAYOUT ENGINE
-- ============================================================================

-- Calculates optimal tooltip placement to avoid screen edges and the Status Bar.
local function FitAroundLocation(bp, loc, maxWidth, maxHeight)
    local ScreenLoc = ScreenLocFromBufLoc(bp, loc)
    local bufView = bp:BufView()
    local infoBarY = micro.InfoBar():GetView().Y

    maxWidth = math.max(1, maxWidth)
    maxHeight = math.max(1, maxHeight)

    local x = bp:VLocFromLoc(loc).VisualX + maxWidth < bufView.Width and ScreenLoc.X or bufView.X + bufView.Width -
                  maxWidth

    local y = ScreenLoc.Y + 1

    local spaceAbove = ScreenLoc.Y - bufView.Y
    -- Safety margin (-1) to avoid rendering over the InfoBar
    local spaceBelow = infoBarY - y - 1

    local width, height = maxWidth, maxHeight

    if spaceBelow < height then
        if spaceAbove > spaceBelow then
            -- Prefer placement above if more space is available
            height = math.min(height, spaceAbove)
            y = ScreenLoc.Y - height
        else
            -- Clip height to available space below
            height = spaceBelow
        end
    end

    x = math.max(0, x)
    y = math.max(0, y)
    height = math.max(1, height)

    return x, y, width, height
end

-- ============================================================================
-- 7. COMPLETION LOGIC
-- ============================================================================

function completionAction(bp)
    if cmd == nil then
        return
    end
    local file = bp.Buf.AbsPath
    local line = bp.Buf:GetActiveCursor().Y
    local char = bp.Buf:GetActiveCursor().X

    currentAction = {
        method = "textDocument/completion",
        response = function(bp, data)
            handleCompletionResults(bp, data)
        end
    }
    send(currentAction.method, fmt.Sprintf(
        '{"textDocument": {"uri": "file://%s"}, "position": {"line": %.0f, "character": %.0f}}', file, line, char))
end

function handleCompletionResults(bp, data)
    local results = data.result
    if not results then
        CloseTooltip();
        return
    end
    if results.items then
        results = results.items
    end
    if #results == 0 then
        CloseTooltip();
        return
    end

    local prefix = getWordPrefix(bp)
    local filtered = {}

    -- Client-side fuzzy filtering
    for _, item in ipairs(results) do
        local label = item.label
        if string.lower(label):find(string.lower(prefix), 1, true) then
            table.insert(filtered, item)
        end
    end

    if #filtered == 0 then
        filtered = results
    end

    table.sort(filtered, function(left, right)
        return (left.sortText or left.label) < (right.sortText or right.label)
    end)

    completionResults = filtered
    if selectedIndex > #completionResults then
        selectedIndex = 1
    end
    scrollOffset = 0

    ShowAutocompleteTooltip(bp)
end

function ShowAutocompleteTooltip(bp)
    local maxWidth = 0
    for _, item in ipairs(completionResults) do
        local label = item.label
        local len = 0
        local status, ccount = pcall(util.CharacterCountInString, label)
        if status then
            len = ccount
        else
            len = #label
        end
        if len > maxWidth then
            maxWidth = len
        end
    end
    maxWidth = maxWidth + 4

    local reqHeight = math.min(#completionResults, 10)

    local prefixLen = 0
    local status, plen = pcall(util.CharacterCountInString, getWordPrefix(bp))
    if status then
        prefixLen = plen
    end
    local loc = buffer.Loc(bp.Cursor.X - prefixLen, bp.Cursor.Y)

    local x, y, realWidth, realHeight = FitAroundLocation(bp, loc, maxWidth, reqHeight)

    -- Dynamic Viewport Pagination
    local pageSize = realHeight

    if selectedIndex > scrollOffset + pageSize then
        scrollOffset = selectedIndex - pageSize
    elseif selectedIndex <= scrollOffset then
        scrollOffset = selectedIndex - 1
    end

    if scrollOffset < 0 then
        scrollOffset = 0
    end
    if #completionResults >= pageSize then
        if scrollOffset > #completionResults - pageSize then
            scrollOffset = #completionResults - pageSize
        end
    end

    local content = ""
    local startIdx = scrollOffset + 1
    local endIdx = math.min(scrollOffset + pageSize, #completionResults)

    for i = startIdx, endIdx do
        local item = completionResults[i]
        local label = item.label
        if i == selectedIndex then
            label = "> " .. label
        else
            label = "  " .. label
        end
        content = content .. label .. "\n"
    end

    if #content > 0 then
        content = content:sub(1, -2)
    end

    if not activeTooltip then
        activeTooltip = Tooltip.new("completion", content, x, y, realWidth, realHeight)
        -- Hijack Keys for Tooltip Navigation
        config.TryBindKey("Enter", "command:lsppp_confirm", true)
        config.TryBindKey("Tab", "command:lsppp_confirm", true)
        config.TryBindKey("Esc", "command:lsppp_escape", true)
        config.TryBindKey("Backspace", "command:lsppp_backspace", true)

        -- Bind Scroll keys to escape (prevents floating tooltip on scroll)
        config.TryBindKey("MouseWheelUp", "command:lsppp_escape", true)
        config.TryBindKey("MouseWheelDown", "command:lsppp_escape", true)
        config.TryBindKey("PageUp", "command:lsppp_escape", true)
        config.TryBindKey("PageDown", "command:lsppp_escape", true)
    else
        activeTooltip:Update(content, x, y, realWidth, realHeight)
    end
end

function CloseTooltip()
    -- Restore Default Keybindings
    config.TryBindKey("Enter", "InsertNewline", true)
    config.TryBindKey("Tab", "IndentSelection,InsertTab", true)
    config.TryBindKey("Esc", "Escape", true)
    config.TryBindKey("Backspace", "Backspace", true)
    -- Fix: Map scroll keys back to their correct actions
    config.TryBindKey("MouseWheelUp", "ScrollUp", true)
    config.TryBindKey("MouseWheelDown", "ScrollDown", true)
    config.TryBindKey("PageUp", "PageUp", true)
    config.TryBindKey("PageDown", "PageDown", true)

    if activeTooltip then
        activeTooltip:Close()
        activeTooltip = nil
        completionResults = {}
        selectedIndex = 1
        scrollOffset = 0
    end
end

-- ============================================================================
-- 8. INTERACTION CALLBACKS
-- ============================================================================

function cycleSelection(delta)
    if not activeTooltip then
        return
    end
    selectedIndex = selectedIndex + delta
    if selectedIndex < 1 then
        selectedIndex = #completionResults
    end
    if selectedIndex > #completionResults then
        selectedIndex = 1
    end
    ShowAutocompleteTooltip(micro.CurPane())
end

function backspaceAction(bp)
    if not activeTooltip then
        bp:Backspace();
        return
    end
    bp:Backspace()
    didChange(bp.Buf)
    local prefix = getWordPrefix(bp)
    if prefix == "" then
        CloseTooltip()
    else
        completionAction(bp)
    end
end

function ConfirmCompletion(bp)
    if not activeTooltip then
        return
    end
    if #completionResults == 0 then
        CloseTooltip();
        return
    end

    local item = completionResults[selectedIndex]
    if item then
        local textToInsert = item.insertText or item.label
        local prefix = getWordPrefix(bp)
        local curX = bp.Cursor.X
        local curY = bp.Cursor.Y

        if #prefix > 0 then
            local startLoc = buffer.Loc(curX - #prefix, curY)
            local endLoc = buffer.Loc(curX, curY)
            bp.Buf:Remove(startLoc, endLoc)
        end
        local insertLoc = buffer.Loc(bp.Cursor.X, bp.Cursor.Y)
        bp.Buf:Insert(insertLoc, textToInsert)
    end
    CloseTooltip()
end

-- Use hooks for navigation to prevent cursor movement conflict
function preCursorUp(bp)
    if activeTooltip then
        cycleSelection(-1);
        return false
    end
    return true
end
function preCursorDown(bp)
    if activeTooltip then
        cycleSelection(1);
        return false
    end
    return true
end
function preInsertNewline(bp)
    if activeTooltip then
        ConfirmCompletion(bp);
        return false
    end
    return true
end
function preIndentSelection(bp)
    if activeTooltip then
        ConfirmCompletion(bp);
        return false
    end
    return true
end

function preAddTab(_)
    CloseTooltip()
    return true
end
function prePreviousTab()
    CloseTooltip()
    return true
end
function preNextTab()
    CloseTooltip()
    return true
end
function onBufferOpen(_)
    CloseTooltip()
end

function onRune(bp, r)
    local ft = bp.Buf:FileType()
    if (ft == "c" or ft == "cpp" or ft == "c++") and cmd then
        micro.After(0, function()
            didChange(bp.Buf)
            if config.GetGlobalOption("lsppp.autocomplete") then
                if r:match("[%w_]") then
                    completionAction(bp)
                else
                    CloseTooltip()
                end
            end
        end)
    end
end

-- ============================================================================
-- 9. FORMATTING
-- ============================================================================

function formatAction(bp)
    if cmd == nil then
        return
    end
    didChange(bp.Buf)
    local file = bp.Buf.AbsPath;
    local cfg = bp.Buf.Settings
    currentAction = {
        method = "textDocument/formatting",
        response = function(bp, data)
            if data.result == nil or #data.result == 0 then
                micro.InfoBar():Message("LSP++: No formatting changes");
                return
            end
            local edits = data.result
            -- Reverse sort edits to ensure line integrity during processing
            table.sort(edits, function(left, right)
                if left.range.start.line ~= right.range.start.line then
                    return left.range.start.line > right.range.start.line
                end
                return left.range.start.character > right.range.start.character
            end)
            local xy = buffer.Loc(bp.Cursor.X, bp.Cursor.Y);
            isFormatting = true
            for _, edit in ipairs(edits) do
                local rangeStart = buffer.Loc(edit.range.start.character, edit.range.start.line)
                local rangeEnd = buffer.Loc(edit.range['end'].character, edit.range['end'].line)
                bp.Buf:Remove(rangeStart, rangeEnd)
                if edit.newText ~= "" then
                    bp.Buf:Insert(rangeStart, edit.newText)
                end
            end
            didChange(bp.Buf);
            bp:Save();
            isFormatting = false;
            bp.Cursor:GotoLoc(xy);
            micro.InfoBar():Message("LSP++: Formatted")
        end
    }
    send(currentAction.method,
        fmt.Sprintf('{"textDocument": {"uri": "file://%s"}, "options": {"tabSize": %.0f, "insertSpaces": %t}}', file,
            cfg["tabsize"] or 4, cfg["tabstospaces"] or true))
end

-- ============================================================================
-- 10. SERVER LIFECYCLE
-- ============================================================================

function startServer(bp)
    if cmd then
        micro.InfoBar():Message("LSP++: Server already running");
        return
    end
    local wd, _ = go_os.Getwd();
    rootUri = fmt.Sprintf("file://%s", wd);
    requestId = 0;
    message = ''
    -- Note: We still spawn 'clangd' as the executable
    cmd = shell.JobSpawn("clangd", {"--background-index", "--header-insertion=never"}, onStdout, onStderr, onExit, {})
    if cmd then
        currentAction = {
            method = "initialize",
            response = function(bp, data)
                send("initialized", "{}", true);
                capabilities = data.result and data.result.capabilities or {};
                micro.InfoBar():Message("LSP++: Server Initialized");
                if bp and bp.Buf then
                    handleInitialized(bp.Buf)
                end
            end
        }
        send(currentAction.method, fmt.Sprintf(
            '{"processId": %.0f, "rootUri": "%s", "capabilities": {"textDocument": {"completion": {"completionItem": {"snippetSupport": false}}, "formatting": {}, "definition": {}, "references": {}}}}',
            go_os.Getpid(), rootUri))
    end
end

function stopServer(bp)
    if cmd then
        shell.JobStop(cmd);
        cmd = nil;
        currentAction = {};
        micro.InfoBar():Message("LSP++: Server Stopped")
    end
end

function handleInitialized(buf)
    if cmd == nil then
        return
    end
    local uri = getUriFromBuf(buf)
    local content = util.String(buf:Bytes()):gsub("\\", "\\\\"):gsub("\n", "\\n"):gsub("\r", "\\r"):gsub('"', '\\"')
        :gsub("\t", "\\t")
    local lang = "c";
    local ft = buf:FileType();
    if ft == "cpp" or ft == "c++" then
        lang = "cpp"
    end
    send("textDocument/didOpen", fmt.Sprintf(
        '{"textDocument": {"uri": "%s", "languageId": "%s", "version": 1, "text": "%s"}}', uri, lang, content), true)
end

function didChange(buf)
    if cmd == nil then
        return
    end
    local uri = getUriFromBuf(buf)
    local content = util.String(buf:Bytes()):gsub("\\", "\\\\"):gsub("\n", "\\n"):gsub("\r", "\\r"):gsub('"', '\\"')
        :gsub("\t", "\\t")
    version[uri] = (version[uri] or 0) + 1
    send("textDocument/didChange",
        fmt.Sprintf('{"textDocument": {"version": %.0f, "uri": "%s"}, "contentChanges": [{"text": "%s"}]}',
            version[uri], uri, content), true)
end

function didSave(buf)
    if cmd == nil then
        return
    end
    local uri = getUriFromBuf(buf);
    send("textDocument/didSave", fmt.Sprintf('{"textDocument": {"uri": "%s"}}', uri), true)
end

function handleDiagnostics(params)
    local pane = micro.CurPane();
    if not pane or not pane.Buf then
        return
    end
    local bp = pane.Buf;
    local uri = getUriFromBuf(bp);
    if params.uri ~= uri then
        return
    end

    -- Use 'lsppp' owner for diagnostics
    bp:ClearMessages("lsppp")
    for _, diagnostic in ipairs(params.diagnostics or {}) do
        local msgType = buffer.MTInfo
        if diagnostic.severity == 1 then
            msgType = buffer.MTError
        elseif diagnostic.severity == 2 then
            msgType = buffer.MTWarning
        end
        local mstart = buffer.Loc(diagnostic.range.start.character, diagnostic.range.start.line)
        local mend = buffer.Loc(diagnostic.range["end"].character, diagnostic.range["end"].line)
        local msg = buffer.NewMessage("lsppp", diagnostic.message, mstart, mend, msgType)
        bp:AddMessage(msg)
    end
end

function onBufferOpen(buf)
    local ft = buf:FileType()
    if (ft == "c" or ft == "cpp" or ft == "c++") and config.GetGlobalOption("lsppp.autostart") then
        if not cmd then
            micro.After(100000000, function()
                local pane = micro.CurPane();
                if pane then
                    startServer(pane)
                end
            end)
        else
            handleInitialized(buf)
        end
    end
end

function onSave(bp)
    if isFormatting then
        return
    end
    local ft = bp.Buf:FileType()
    if ft == "c" or ft == "cpp" or ft == "c++" then
        if config.GetGlobalOption("lsppp.autoformat") and cmd then
            formatAction(bp)
        end
        didSave(bp.Buf)
    end
end

function definitionAction(bp)
    if cmd == nil then
        return
    end
    local file = bp.Buf.AbsPath;
    local line = bp.Buf:GetActiveCursor().Y;
    local char = bp.Buf:GetActiveCursor().X
    currentAction = {
        method = "textDocument/definition",
        response = function(bp, data)
            local results = data.result
            if results == nil or (type(results) == "table" and #results == 0) then
                micro.InfoBar():Message("LSP++: No definition found");
                return
            end
            if results.uri ~= nil then
                results = {results}
            end
            local uri = results[1].uri;
            local doc = uri:gsub("^file://", "");
            local range = results[1].range
            if file ~= doc then
                local buf, _ = buffer.NewBufferFromFile(doc);
                bp:AddTab();
                micro.CurPane():OpenBuffer(buf)
            end
            bp.Buf:GetActiveCursor():GotoLoc(buffer.Loc(range.start.character, range.start.line));
            bp:Center()
        end
    }
    send(currentAction.method, fmt.Sprintf(
        '{"textDocument": {"uri": "file://%s"}, "position": {"line": %.0f, "character": %.0f}}', file, line, char))
end

function referencesAction(bp)
    if cmd == nil then
        return
    end
    local file = bp.Buf.AbsPath;
    local line = bp.Buf:GetActiveCursor().Y;
    local char = bp.Buf:GetActiveCursor().X
    currentAction = {
        method = "textDocument/references",
        response = function(bp, data)
            if data.result == nil or #data.result == 0 then
                micro.InfoBar():Message("LSP++: No references found");
                return
            end
            local msg = '';
            for _, ref in ipairs(data.result) do
                if msg ~= '' then
                    msg = msg .. '\n'
                end
                local doc = ref.uri;
                msg = msg .. "." .. doc:sub(#rootUri + 1) .. ":" .. ref.range.start.line .. ":" ..
                          ref.range.start.character
            end
            local logBuf = buffer.NewBuffer(msg, "References");
            bp:HSplitBuf(logBuf)
        end
    }
    send(currentAction.method, fmt.Sprintf(
        '{"textDocument": {"uri": "file://%s"}, "position": {"line": %.0f, "character": %.0f}, "context": {"includeDeclaration": true}}',
        file, line, char))
end
