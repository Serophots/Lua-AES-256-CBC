
--AES-256-CBC encryption algorithm, taken from Lua Lockbox
--https://github.com/somesocks/lua-lockbox

--Added my own custom HexPadding so you can input raw strings of any length. It works similar to Base64 padding

-- It does use standardised AES-CBC, just ensure to replicate the encoding/decoding if your planning on decrypting in another language

--Usage at bottom. Ensure you update PadCharacter to be something that wont appear in the text your encrypting
local crypt = {}; do
    local M = {}; do --bit library
        M = {_TYPE='module', _NAME='bit.numberlua', _VERSION='0.3.1.20120131'}

        local floor = math.floor

        local MOD = 2^32
        local MODM = MOD-1

        local function memoize(f)
        local mt = {}
        local t = setmetatable({}, mt)
        function mt:__index(k)
            local v = f(k); t[k] = v
            return v
        end
        return t
        end

        local function make_bitop_uncached(t, m)
        local function bitop(a, b)
            local res,p = 0,1
            while a ~= 0 and b ~= 0 do
            local am, bm = a%m, b%m
            res = res + t[am][bm]*p
            a = (a - am) / m
            b = (b - bm) / m
            p = p*m
            end
            res = res + (a+b)*p
            return res
        end
        return bitop
        end

        local function make_bitop(t)
        local op1 = make_bitop_uncached(t,2^1)
        local op2 = memoize(function(a)
            return memoize(function(b)
            return op1(a, b)
            end)
        end)
        return make_bitop_uncached(op2, 2^(t.n or 1))
        end

        -- ok?  probably not if running on a 32-bit int Lua number type platform
        function M.tobit(x)
        return x % 2^32
        end

        M.bxor = make_bitop {[0]={[0]=0,[1]=1},[1]={[0]=1,[1]=0}, n=4}
        local bxor = M.bxor

        function M.bnot(a)   return MODM - a end
        local bnot = M.bnot

        function M.band(a,b) return ((a+b) - bxor(a,b))/2 end
        local band = M.band

        function M.bor(a,b)  return MODM - band(MODM - a, MODM - b) end
        local bor = M.bor

        local lshift, rshift -- forward declare

        function M.rshift(a,disp) -- Lua5.2 insipred
        if disp < 0 then return lshift(a,-disp) end
        return floor(a % 2^32 / 2^disp)
        end
        rshift = M.rshift

        function M.lshift(a,disp) -- Lua5.2 inspired
        if disp < 0 then return rshift(a,-disp) end 
        return (a * 2^disp) % 2^32
        end
        lshift = M.lshift

        function M.tohex(x, n) -- BitOp style
        n = n or 8
        local up
        if n <= 0 then
            if n == 0 then return '' end
            up = true
            n = - n
        end
        x = band(x, 16^n-1)
        return ('%0'..n..(up and 'X' or 'x')):format(x)
        end
        local tohex = M.tohex

        function M.extract(n, field, width) -- Lua5.2 inspired
        width = width or 1
        return band(rshift(n, field), 2^width-1)
        end
        local extract = M.extract

        function M.replace(n, v, field, width) -- Lua5.2 inspired
        width = width or 1
        local mask1 = 2^width-1
        v = band(v, mask1) -- required by spec?
        local mask = bnot(lshift(mask1, field))
        return band(n, mask) + lshift(v, field)
        end
        local replace = M.replace

        function M.bswap(x)  -- BitOp style
        local a = band(x, 0xff); x = rshift(x, 8)
        local b = band(x, 0xff); x = rshift(x, 8)
        local c = band(x, 0xff); x = rshift(x, 8)
        local d = band(x, 0xff)
        return lshift(lshift(lshift(a, 8) + b, 8) + c, 8) + d
        end
        local bswap = M.bswap

        function M.rrotate(x, disp)  -- Lua5.2 inspired
        disp = disp % 32
        local low = band(x, 2^disp-1)
        return rshift(x, disp) + lshift(low, 32-disp)
        end
        local rrotate = M.rrotate

        function M.lrotate(x, disp)  -- Lua5.2 inspired
        return rrotate(x, -disp)
        end
        local lrotate = M.lrotate

        M.rol = M.lrotate  -- LuaOp inspired
        M.ror = M.rrotate  -- LuaOp insipred


        function M.arshift(x, disp) -- Lua5.2 inspired
        local z = rshift(x, disp)
        if x >= 0x80000000 then z = z + lshift(2^disp-1, 32-disp) end
        return z
        end
        local arshift = M.arshift

        function M.btest(x, y) -- Lua5.2 inspired
        return band(x, y) ~= 0
        end

        --
        -- Start Lua 5.2 "bit32" compat section.
        --

        M.bit32 = {} -- Lua 5.2 'bit32' compatibility


        local function bit32_bnot(x)
        return (-1 - x) % MOD
        end
        M.bit32.bnot = bit32_bnot

        local function bit32_bxor(a, b, c, ...)
        local z
        if b then
            a = a % MOD
            b = b % MOD
            z = bxor(a, b)
            if c then
            z = bit32_bxor(z, c, ...)
            end
            return z
        elseif a then
            return a % MOD
        else
            return 0
        end
        end
        M.bit32.bxor = bit32_bxor

        local function bit32_band(a, b, c, ...)
        local z
        if b then
            a = a % MOD
            b = b % MOD
            z = ((a+b) - bxor(a,b)) / 2
            if c then
            z = bit32_band(z, c, ...)
            end
            return z
        elseif a then
            return a % MOD
        else
            return MODM
        end
        end
        M.bit32.band = bit32_band

        local function bit32_bor(a, b, c, ...)
        local z
        if b then
            a = a % MOD
            b = b % MOD
            z = MODM - band(MODM - a, MODM - b)
            if c then
            z = bit32_bor(z, c, ...)
            end
            return z
        elseif a then
            return a % MOD
        else
            return 0
        end
        end
        M.bit32.bor = bit32_bor

        function M.bit32.btest(...)
        return bit32_band(...) ~= 0
        end

        function M.bit32.lrotate(x, disp)
        return lrotate(x % MOD, disp)
        end

        function M.bit32.rrotate(x, disp)
        return rrotate(x % MOD, disp)
        end

        function M.bit32.lshift(x,disp)
        if disp > 31 or disp < -31 then return 0 end
        return lshift(x % MOD, disp)
        end

        function M.bit32.rshift(x,disp)
        if disp > 31 or disp < -31 then return 0 end
        return rshift(x % MOD, disp)
        end

        function M.bit32.arshift(x,disp)
        x = x % MOD
        if disp >= 0 then
            if disp > 31 then
            return (x >= 0x80000000) and MODM or 0
            else
            local z = rshift(x, disp)
            if x >= 0x80000000 then z = z + lshift(2^disp-1, 32-disp) end
            return z
            end
        else
            return lshift(x, -disp)
        end
        end

        function M.bit32.extract(x, field, ...)
        local width = ... or 1
        if field < 0 or field > 31 or width < 0 or field+width > 32 then error 'out of range' end
        x = x % MOD
        return extract(x, field, ...)
        end

        function M.bit32.replace(x, v, field, ...)
        local width = ... or 1
        if field < 0 or field > 31 or width < 0 or field+width > 32 then error 'out of range' end
        x = x % MOD
        v = v % MOD
        return replace(x, v, field, ...)
        end


        --
        -- Start LuaBitOp "bit" compat section.
        --

        M.bit = {} -- LuaBitOp "bit" compatibility

        function M.bit.tobit(x)
        x = x % MOD
        if x >= 0x80000000 then x = x - MOD end
        return x
        end
        local bit_tobit = M.bit.tobit

        function M.bit.tohex(x, ...)
        return tohex(x % MOD, ...)
        end

        function M.bit.bnot(x)
        return bit_tobit(bnot(x % MOD))
        end

        local function bit_bor(a, b, c, ...)
        if c then
            return bit_bor(bit_bor(a, b), c, ...)
        elseif b then
            return bit_tobit(bor(a % MOD, b % MOD))
        else
            return bit_tobit(a)
        end
        end
        M.bit.bor = bit_bor

        local function bit_band(a, b, c, ...)
        if c then
            return bit_band(bit_band(a, b), c, ...)
        elseif b then
            return bit_tobit(band(a % MOD, b % MOD))
        else
            return bit_tobit(a)
        end
        end
        M.bit.band = bit_band

        local function bit_bxor(a, b, c, ...)
        if c then
            return bit_bxor(bit_bxor(a, b), c, ...)
        elseif b then
            return bit_tobit(bxor(a % MOD, b % MOD))
        else
            return bit_tobit(a)
        end
        end
        M.bit.bxor = bit_bxor

        function M.bit.lshift(x, n)
        return bit_tobit(lshift(x % MOD, n % 32))
        end

        function M.bit.rshift(x, n)
        return bit_tobit(rshift(x % MOD, n % 32))
        end

        function M.bit.arshift(x, n)
        return bit_tobit(arshift(x % MOD, n % 32))
        end

        function M.bit.rol(x, n)
        return bit_tobit(lrotate(x % MOD, n % 32))
        end

        function M.bit.ror(x, n)
        return bit_tobit(rrotate(x % MOD, n % 32))
        end

        function M.bit.bswap(x)
        return bit_tobit(bswap(x % MOD))
        end
    end

    local Queue = function()
        local queue = {};
        local tail = 0;
        local head = 0;

        local public = {};

        public.push = function(obj)
            queue[head] = obj;
            head = head + 1;
            return;
        end

        public.pop = function()
            if tail < head then
                local obj = queue[tail];
                queue[tail] = nil;
                tail = tail + 1;
                return obj;
            else
                return nil;
            end
        end

        public.size = function()
            return head - tail;
        end

        public.getHead = function()
            return head;
        end

        public.getTail = function()
            return tail;
        end

        public.reset = function()
            queue = {};
            head = 0;
            tail = 0;
        end

        return public;
    end

    local Array = {} do
        local String = string;

        local XOR = M.bxor;

        Array.size = function(array)
            return #array;
        end

        Array.fromString = function(string)
            local bytes = {};

            local i = 1;
            local byte = String.byte(string, i);
            while byte ~= nil do
                bytes[i] = byte;
                i = i + 1;
                byte = String.byte(string, i);
            end

            return bytes;

        end

        Array.toString = function(bytes)
            local chars = {};
            local i = 1;

            local byte = bytes[i];
            while byte ~= nil do
                chars[i] = String.char(byte);
                i = i + 1;
                byte = bytes[i];
            end

            return table.concat(chars, "");
        end

        Array.fromStream = function(stream)
            local array = {};
            local i = 1;

            local byte = stream();
            while byte ~= nil do
                array[i] = byte;
                i = i + 1;
                byte = stream();
            end

            return array;
        end

        Array.readFromQueue = function(queue, size)
            local array = {};

            for i = 1, size do
                array[i] = queue.pop();
            end

            return array;
        end

        Array.writeToQueue = function(queue, array)
            local size = Array.size(array);

            for i = 1, size do
                queue.push(array[i]);
            end
        end

        Array.toStream = function(array)
            local queue = Queue();
            local i = 1;

            local byte = array[i];
            while byte ~= nil do
                queue.push(byte);
                i = i + 1;
                byte = array[i];
            end

            return queue.pop;
        end


        local fromHexTable = {};
        for i = 0, 255 do
            fromHexTable[String.format("%02X", i)] = i;
            fromHexTable[String.format("%02x", i)] = i;
        end

        Array.fromHex = function(hex)
            local array = {};

            for i = 1, String.len(hex) / 2 do
                local h = String.sub(hex, i * 2 - 1, i * 2);
                array[i] = fromHexTable[h];
            end

            return array;
        end


        local toHexTable = {};
        for i = 0, 255 do
            toHexTable[i] = String.format("%02X", i);
        end

        Array.toHex = function(array)
            local hex = {};
            local i = 1;

            local byte = array[i];
            while byte ~= nil do
                hex[i] = toHexTable[byte];
                i = i + 1;
                byte = array[i];
            end

            return table.concat(hex, "");

        end

        Array.concat = function(a, b)
            local concat = {};
            local out = 1;

            local i = 1;
            local byte = a[i];
            while byte ~= nil do
                concat[out] = byte;
                i = i + 1;
                out = out + 1;
                byte = a[i];
            end

            i = 1;
            byte = b[i];
            while byte ~= nil do
                concat[out] = byte;
                i = i + 1;
                out = out + 1;
                byte = b[i];
            end

            return concat;
        end

        Array.truncate = function(a, newSize)
            local x = {};

            for i = 1, newSize do
                x[i] = a[i];
            end

            return x;
        end

        Array.XOR = function(a, b)
            local x = {};

            for k, v in pairs(a) do
                x[k] = XOR(v, b[k]);
            end

            return x;
        end

        Array.substitute = function(input, sbox)
            local out = {};

            for k, v in pairs(input) do
                out[k] = sbox[v];
            end

            return out;
        end

        Array.permute = function(input, pbox)
            local out = {};

            for k, v in pairs(pbox) do
                out[k] = input[v];
            end

            return out;
        end

        Array.copy = function(input)
            local out = {};

            for k, v in pairs(input) do
                out[k] = v;
            end
            return out;
        end

        Array.slice = function(input, start, stop)
            local out = {};

            for i = start, stop do
                out[i - start + 1] = input[i];
            end
            return out;
        end
    end

    local Stream = {}; do
        local String = string
        Stream.fromString = function(string)
            local i = 0;
            return function()
                i = i + 1;
                return String.byte(string, i);
            end
        end

        Stream.toString = function(stream)
            local array = {};
            local i = 1;

            local byte = stream();
            while byte ~= nil do
                array[i] = String.char(byte);
                i = i + 1;
                byte = stream();
            end

            return table.concat(array);
        end

        Stream.fromArray = function(array)
            local queue = Queue();
            local i = 1;

            local byte = array[i];
            while byte ~= nil do
                queue.push(byte);
                i = i + 1;
                byte = array[i];
            end

            return queue.pop;
        end

        Stream.toArray = function(stream)
            local array = {};
            local i = 1;

            local byte = stream();
            while byte ~= nil do
                array[i] = byte;
                i = i + 1;
                byte = stream();
            end

            return array;
        end

        local fromHexTable = {};
        for i = 0, 255 do
            fromHexTable[String.format("%02X", i)] = i;
            fromHexTable[String.format("%02x", i)] = i;
        end

        Stream.fromHex = function(hex)
            local queue = Queue();

            for i = 1, String.len(hex) / 2 do
                local h = String.sub(hex, i * 2 - 1, i * 2);
                queue.push(fromHexTable[h]);
            end

            return queue.pop;
        end

        local toHexTable = {};
        for i = 0, 255 do
            toHexTable[i] = String.format("%02X", i);
        end

        Stream.toHex = function(stream)
            local hex = {};
            local i = 1;

            local byte = stream();
            while byte ~= nil do
                hex[i] = toHexTable[byte];
                i = i + 1;
                byte = stream();
            end

            return table.concat(hex);
        end
    end

    local AES = {}; do
        local XOR = M.bxor;

        local SBOX = {
            [0] = 0x63, 0x7C, 0x77, 0x7B, 0xF2, 0x6B, 0x6F, 0xC5, 0x30, 0x01, 0x67, 0x2B, 0xFE, 0xD7, 0xAB, 0x76,
            0xCA, 0x82, 0xC9, 0x7D, 0xFA, 0x59, 0x47, 0xF0, 0xAD, 0xD4, 0xA2, 0xAF, 0x9C, 0xA4, 0x72, 0xC0,
            0xB7, 0xFD, 0x93, 0x26, 0x36, 0x3F, 0xF7, 0xCC, 0x34, 0xA5, 0xE5, 0xF1, 0x71, 0xD8, 0x31, 0x15,
            0x04, 0xC7, 0x23, 0xC3, 0x18, 0x96, 0x05, 0x9A, 0x07, 0x12, 0x80, 0xE2, 0xEB, 0x27, 0xB2, 0x75,
            0x09, 0x83, 0x2C, 0x1A, 0x1B, 0x6E, 0x5A, 0xA0, 0x52, 0x3B, 0xD6, 0xB3, 0x29, 0xE3, 0x2F, 0x84,
            0x53, 0xD1, 0x00, 0xED, 0x20, 0xFC, 0xB1, 0x5B, 0x6A, 0xCB, 0xBE, 0x39, 0x4A, 0x4C, 0x58, 0xCF,
            0xD0, 0xEF, 0xAA, 0xFB, 0x43, 0x4D, 0x33, 0x85, 0x45, 0xF9, 0x02, 0x7F, 0x50, 0x3C, 0x9F, 0xA8,
            0x51, 0xA3, 0x40, 0x8F, 0x92, 0x9D, 0x38, 0xF5, 0xBC, 0xB6, 0xDA, 0x21, 0x10, 0xFF, 0xF3, 0xD2,
            0xCD, 0x0C, 0x13, 0xEC, 0x5F, 0x97, 0x44, 0x17, 0xC4, 0xA7, 0x7E, 0x3D, 0x64, 0x5D, 0x19, 0x73,
            0x60, 0x81, 0x4F, 0xDC, 0x22, 0x2A, 0x90, 0x88, 0x46, 0xEE, 0xB8, 0x14, 0xDE, 0x5E, 0x0B, 0xDB,
            0xE0, 0x32, 0x3A, 0x0A, 0x49, 0x06, 0x24, 0x5C, 0xC2, 0xD3, 0xAC, 0x62, 0x91, 0x95, 0xE4, 0x79,
            0xE7, 0xC8, 0x37, 0x6D, 0x8D, 0xD5, 0x4E, 0xA9, 0x6C, 0x56, 0xF4, 0xEA, 0x65, 0x7A, 0xAE, 0x08,
            0xBA, 0x78, 0x25, 0x2E, 0x1C, 0xA6, 0xB4, 0xC6, 0xE8, 0xDD, 0x74, 0x1F, 0x4B, 0xBD, 0x8B, 0x8A,
            0x70, 0x3E, 0xB5, 0x66, 0x48, 0x03, 0xF6, 0x0E, 0x61, 0x35, 0x57, 0xB9, 0x86, 0xC1, 0x1D, 0x9E,
            0xE1, 0xF8, 0x98, 0x11, 0x69, 0xD9, 0x8E, 0x94, 0x9B, 0x1E, 0x87, 0xE9, 0xCE, 0x55, 0x28, 0xDF,
            0x8C, 0xA1, 0x89, 0x0D, 0xBF, 0xE6, 0x42, 0x68, 0x41, 0x99, 0x2D, 0x0F, 0xB0, 0x54, 0xBB, 0x16};

        local ISBOX = {
            [0] = 0x52, 0x09, 0x6A, 0xD5, 0x30, 0x36, 0xA5, 0x38, 0xBF, 0x40, 0xA3, 0x9E, 0x81, 0xF3, 0xD7, 0xFB,
            0x7C, 0xE3, 0x39, 0x82, 0x9B, 0x2F, 0xFF, 0x87, 0x34, 0x8E, 0x43, 0x44, 0xC4, 0xDE, 0xE9, 0xCB,
            0x54, 0x7B, 0x94, 0x32, 0xA6, 0xC2, 0x23, 0x3D, 0xEE, 0x4C, 0x95, 0x0B, 0x42, 0xFA, 0xC3, 0x4E,
            0x08, 0x2E, 0xA1, 0x66, 0x28, 0xD9, 0x24, 0xB2, 0x76, 0x5B, 0xA2, 0x49, 0x6D, 0x8B, 0xD1, 0x25,
            0x72, 0xF8, 0xF6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xD4, 0xA4, 0x5C, 0xCC, 0x5D, 0x65, 0xB6, 0x92,
            0x6C, 0x70, 0x48, 0x50, 0xFD, 0xED, 0xB9, 0xDA, 0x5E, 0x15, 0x46, 0x57, 0xA7, 0x8D, 0x9D, 0x84,
            0x90, 0xD8, 0xAB, 0x00, 0x8C, 0xBC, 0xD3, 0x0A, 0xF7, 0xE4, 0x58, 0x05, 0xB8, 0xB3, 0x45, 0x06,
            0xD0, 0x2C, 0x1E, 0x8F, 0xCA, 0x3F, 0x0F, 0x02, 0xC1, 0xAF, 0xBD, 0x03, 0x01, 0x13, 0x8A, 0x6B,
            0x3A, 0x91, 0x11, 0x41, 0x4F, 0x67, 0xDC, 0xEA, 0x97, 0xF2, 0xCF, 0xCE, 0xF0, 0xB4, 0xE6, 0x73,
            0x96, 0xAC, 0x74, 0x22, 0xE7, 0xAD, 0x35, 0x85, 0xE2, 0xF9, 0x37, 0xE8, 0x1C, 0x75, 0xDF, 0x6E,
            0x47, 0xF1, 0x1A, 0x71, 0x1D, 0x29, 0xC5, 0x89, 0x6F, 0xB7, 0x62, 0x0E, 0xAA, 0x18, 0xBE, 0x1B,
            0xFC, 0x56, 0x3E, 0x4B, 0xC6, 0xD2, 0x79, 0x20, 0x9A, 0xDB, 0xC0, 0xFE, 0x78, 0xCD, 0x5A, 0xF4,
            0x1F, 0xDD, 0xA8, 0x33, 0x88, 0x07, 0xC7, 0x31, 0xB1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xEC, 0x5F,
            0x60, 0x51, 0x7F, 0xA9, 0x19, 0xB5, 0x4A, 0x0D, 0x2D, 0xE5, 0x7A, 0x9F, 0x93, 0xC9, 0x9C, 0xEF,
            0xA0, 0xE0, 0x3B, 0x4D, 0xAE, 0x2A, 0xF5, 0xB0, 0xC8, 0xEB, 0xBB, 0x3C, 0x83, 0x53, 0x99, 0x61,
            0x17, 0x2B, 0x04, 0x7E, 0xBA, 0x77, 0xD6, 0x26, 0xE1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0C, 0x7D};

        local ROW_SHIFT =  {  1,  6, 11, 16,  5, 10, 15,  4,  9, 14,  3,  8, 13,  2,  7, 12, };
        local IROW_SHIFT = {  1, 14, 11,  8,  5,  2, 15, 12,  9,  6,  3, 16, 13, 10,  7,  4, };

        local ETABLE = {
            [0] = 0x01, 0x03, 0x05, 0x0F, 0x11, 0x33, 0x55, 0xFF, 0x1A, 0x2E, 0x72, 0x96, 0xA1, 0xF8, 0x13, 0x35,
            0x5F, 0xE1, 0x38, 0x48, 0xD8, 0x73, 0x95, 0xA4, 0xF7, 0x02, 0x06, 0x0A, 0x1E, 0x22, 0x66, 0xAA,
            0xE5, 0x34, 0x5C, 0xE4, 0x37, 0x59, 0xEB, 0x26, 0x6A, 0xBE, 0xD9, 0x70, 0x90, 0xAB, 0xE6, 0x31,
            0x53, 0xF5, 0x04, 0x0C, 0x14, 0x3C, 0x44, 0xCC, 0x4F, 0xD1, 0x68, 0xB8, 0xD3, 0x6E, 0xB2, 0xCD,
            0x4C, 0xD4, 0x67, 0xA9, 0xE0, 0x3B, 0x4D, 0xD7, 0x62, 0xA6, 0xF1, 0x08, 0x18, 0x28, 0x78, 0x88,
            0x83, 0x9E, 0xB9, 0xD0, 0x6B, 0xBD, 0xDC, 0x7F, 0x81, 0x98, 0xB3, 0xCE, 0x49, 0xDB, 0x76, 0x9A,
            0xB5, 0xC4, 0x57, 0xF9, 0x10, 0x30, 0x50, 0xF0, 0x0B, 0x1D, 0x27, 0x69, 0xBB, 0xD6, 0x61, 0xA3,
            0xFE, 0x19, 0x2B, 0x7D, 0x87, 0x92, 0xAD, 0xEC, 0x2F, 0x71, 0x93, 0xAE, 0xE9, 0x20, 0x60, 0xA0,
            0xFB, 0x16, 0x3A, 0x4E, 0xD2, 0x6D, 0xB7, 0xC2, 0x5D, 0xE7, 0x32, 0x56, 0xFA, 0x15, 0x3F, 0x41,
            0xC3, 0x5E, 0xE2, 0x3D, 0x47, 0xC9, 0x40, 0xC0, 0x5B, 0xED, 0x2C, 0x74, 0x9C, 0xBF, 0xDA, 0x75,
            0x9F, 0xBA, 0xD5, 0x64, 0xAC, 0xEF, 0x2A, 0x7E, 0x82, 0x9D, 0xBC, 0xDF, 0x7A, 0x8E, 0x89, 0x80,
            0x9B, 0xB6, 0xC1, 0x58, 0xE8, 0x23, 0x65, 0xAF, 0xEA, 0x25, 0x6F, 0xB1, 0xC8, 0x43, 0xC5, 0x54,
            0xFC, 0x1F, 0x21, 0x63, 0xA5, 0xF4, 0x07, 0x09, 0x1B, 0x2D, 0x77, 0x99, 0xB0, 0xCB, 0x46, 0xCA,
            0x45, 0xCF, 0x4A, 0xDE, 0x79, 0x8B, 0x86, 0x91, 0xA8, 0xE3, 0x3E, 0x42, 0xC6, 0x51, 0xF3, 0x0E,
            0x12, 0x36, 0x5A, 0xEE, 0x29, 0x7B, 0x8D, 0x8C, 0x8F, 0x8A, 0x85, 0x94, 0xA7, 0xF2, 0x0D, 0x17,
            0x39, 0x4B, 0xDD, 0x7C, 0x84, 0x97, 0xA2, 0xFD, 0x1C, 0x24, 0x6C, 0xB4, 0xC7, 0x52, 0xF6, 0x01};

        local LTABLE = {
            [0] = 0x00, 0x00, 0x19, 0x01, 0x32, 0x02, 0x1A, 0xC6, 0x4B, 0xC7, 0x1B, 0x68, 0x33, 0xEE, 0xDF, 0x03,
            0x64, 0x04, 0xE0, 0x0E, 0x34, 0x8D, 0x81, 0xEF, 0x4C, 0x71, 0x08, 0xC8, 0xF8, 0x69, 0x1C, 0xC1,
            0x7D, 0xC2, 0x1D, 0xB5, 0xF9, 0xB9, 0x27, 0x6A, 0x4D, 0xE4, 0xA6, 0x72, 0x9A, 0xC9, 0x09, 0x78,
            0x65, 0x2F, 0x8A, 0x05, 0x21, 0x0F, 0xE1, 0x24, 0x12, 0xF0, 0x82, 0x45, 0x35, 0x93, 0xDA, 0x8E,
            0x96, 0x8F, 0xDB, 0xBD, 0x36, 0xD0, 0xCE, 0x94, 0x13, 0x5C, 0xD2, 0xF1, 0x40, 0x46, 0x83, 0x38,
            0x66, 0xDD, 0xFD, 0x30, 0xBF, 0x06, 0x8B, 0x62, 0xB3, 0x25, 0xE2, 0x98, 0x22, 0x88, 0x91, 0x10,
            0x7E, 0x6E, 0x48, 0xC3, 0xA3, 0xB6, 0x1E, 0x42, 0x3A, 0x6B, 0x28, 0x54, 0xFA, 0x85, 0x3D, 0xBA,
            0x2B, 0x79, 0x0A, 0x15, 0x9B, 0x9F, 0x5E, 0xCA, 0x4E, 0xD4, 0xAC, 0xE5, 0xF3, 0x73, 0xA7, 0x57,
            0xAF, 0x58, 0xA8, 0x50, 0xF4, 0xEA, 0xD6, 0x74, 0x4F, 0xAE, 0xE9, 0xD5, 0xE7, 0xE6, 0xAD, 0xE8,
            0x2C, 0xD7, 0x75, 0x7A, 0xEB, 0x16, 0x0B, 0xF5, 0x59, 0xCB, 0x5F, 0xB0, 0x9C, 0xA9, 0x51, 0xA0,
            0x7F, 0x0C, 0xF6, 0x6F, 0x17, 0xC4, 0x49, 0xEC, 0xD8, 0x43, 0x1F, 0x2D, 0xA4, 0x76, 0x7B, 0xB7,
            0xCC, 0xBB, 0x3E, 0x5A, 0xFB, 0x60, 0xB1, 0x86, 0x3B, 0x52, 0xA1, 0x6C, 0xAA, 0x55, 0x29, 0x9D,
            0x97, 0xB2, 0x87, 0x90, 0x61, 0xBE, 0xDC, 0xFC, 0xBC, 0x95, 0xCF, 0xCD, 0x37, 0x3F, 0x5B, 0xD1,
            0x53, 0x39, 0x84, 0x3C, 0x41, 0xA2, 0x6D, 0x47, 0x14, 0x2A, 0x9E, 0x5D, 0x56, 0xF2, 0xD3, 0xAB,
            0x44, 0x11, 0x92, 0xD9, 0x23, 0x20, 0x2E, 0x89, 0xB4, 0x7C, 0xB8, 0x26, 0x77, 0x99, 0xE3, 0xA5,
            0x67, 0x4A, 0xED, 0xDE, 0xC5, 0x31, 0xFE, 0x18, 0x0D, 0x63, 0x8C, 0x80, 0xC0, 0xF7, 0x70, 0x07};

        local MIXTABLE = {
            0x02, 0x03, 0x01, 0x01,
            0x01, 0x02, 0x03, 0x01,
            0x01, 0x01, 0x02, 0x03,
            0x03, 0x01, 0x01, 0x02};

        local IMIXTABLE = {
            0x0E, 0x0B, 0x0D, 0x09,
            0x09, 0x0E, 0x0B, 0x0D,
            0x0D, 0x09, 0x0E, 0x0B,
            0x0B, 0x0D, 0x09, 0x0E};

        local RCON = {
            [0] = 0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a,
            0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39,
            0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a,
            0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8,
            0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef,
            0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc,
            0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b,
            0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3,
            0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94,
            0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20,
            0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35,
            0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f,
            0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04,
            0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63,
            0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd,
            0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb, 0x8d};


        local GMUL = function(A, B)
            if(A == 0x01) then return B; end
            if(B == 0x01) then return A; end
            if(A == 0x00) then return 0; end
            if(B == 0x00) then return 0; end

            local LA = LTABLE[A];
            local LB = LTABLE[B];

            local sum = LA + LB;
            if (sum > 0xFF) then sum = sum - 0xFF; end

            return ETABLE[sum];
        end

        local byteSub = Array.substitute;

        local shiftRow = Array.permute;

        local mixCol = function(i, mix)
            local out = {};

            local a, b, c, d;

            a = GMUL(i[ 1], mix[ 1]);
            b = GMUL(i[ 2], mix[ 2]);
            c = GMUL(i[ 3], mix[ 3]);
            d = GMUL(i[ 4], mix[ 4]);
            out[ 1] = XOR(XOR(a, b), XOR(c, d));
            a = GMUL(i[ 1], mix[ 5]);
            b = GMUL(i[ 2], mix[ 6]);
            c = GMUL(i[ 3], mix[ 7]);
            d = GMUL(i[ 4], mix[ 8]);
            out[ 2] = XOR(XOR(a, b), XOR(c, d));
            a = GMUL(i[ 1], mix[ 9]);
            b = GMUL(i[ 2], mix[10]);
            c = GMUL(i[ 3], mix[11]);
            d = GMUL(i[ 4], mix[12]);
            out[ 3] = XOR(XOR(a, b), XOR(c, d));
            a = GMUL(i[ 1], mix[13]);
            b = GMUL(i[ 2], mix[14]);
            c = GMUL(i[ 3], mix[15]);
            d = GMUL(i[ 4], mix[16]);
            out[ 4] = XOR(XOR(a, b), XOR(c, d));


            a = GMUL(i[ 5], mix[ 1]);
            b = GMUL(i[ 6], mix[ 2]);
            c = GMUL(i[ 7], mix[ 3]);
            d = GMUL(i[ 8], mix[ 4]);
            out[ 5] = XOR(XOR(a, b), XOR(c, d));
            a = GMUL(i[ 5], mix[ 5]);
            b = GMUL(i[ 6], mix[ 6]);
            c = GMUL(i[ 7], mix[ 7]);
            d = GMUL(i[ 8], mix[ 8]);
            out[ 6] = XOR(XOR(a, b), XOR(c, d));
            a = GMUL(i[ 5], mix[ 9]);
            b = GMUL(i[ 6], mix[10]);
            c = GMUL(i[ 7], mix[11]);
            d = GMUL(i[ 8], mix[12]);
            out[ 7] = XOR(XOR(a, b), XOR(c, d));
            a = GMUL(i[ 5], mix[13]);
            b = GMUL(i[ 6], mix[14]);
            c = GMUL(i[ 7], mix[15]);
            d = GMUL(i[ 8], mix[16]);
            out[ 8] = XOR(XOR(a, b), XOR(c, d));


            a = GMUL(i[ 9], mix[ 1]);
            b = GMUL(i[10], mix[ 2]);
            c = GMUL(i[11], mix[ 3]);
            d = GMUL(i[12], mix[ 4]);
            out[ 9] = XOR(XOR(a, b), XOR(c, d));
            a = GMUL(i[ 9], mix[ 5]);
            b = GMUL(i[10], mix[ 6]);
            c = GMUL(i[11], mix[ 7]);
            d = GMUL(i[12], mix[ 8]);
            out[10] = XOR(XOR(a, b), XOR(c, d));
            a = GMUL(i[ 9], mix[ 9]);
            b = GMUL(i[10], mix[10]);
            c = GMUL(i[11], mix[11]);
            d = GMUL(i[12], mix[12]);
            out[11] = XOR(XOR(a, b), XOR(c, d));
            a = GMUL(i[ 9], mix[13]);
            b = GMUL(i[10], mix[14]);
            c = GMUL(i[11], mix[15]);
            d = GMUL(i[12], mix[16]);
            out[12] = XOR(XOR(a, b), XOR(c, d));


            a = GMUL(i[13], mix[ 1]);
            b = GMUL(i[14], mix[ 2]);
            c = GMUL(i[15], mix[ 3]);
            d = GMUL(i[16], mix[ 4]);
            out[13] = XOR(XOR(a, b), XOR(c, d));
            a = GMUL(i[13], mix[ 5]);
            b = GMUL(i[14], mix[ 6]);
            c = GMUL(i[15], mix[ 7]);
            d = GMUL(i[16], mix[ 8]);
            out[14] = XOR(XOR(a, b), XOR(c, d));
            a = GMUL(i[13], mix[ 9]);
            b = GMUL(i[14], mix[10]);
            c = GMUL(i[15], mix[11]);
            d = GMUL(i[16], mix[12]);
            out[15] = XOR(XOR(a, b), XOR(c, d));
            a = GMUL(i[13], mix[13]);
            b = GMUL(i[14], mix[14]);
            c = GMUL(i[15], mix[15]);
            d = GMUL(i[16], mix[16]);
            out[16] = XOR(XOR(a, b), XOR(c, d));

            return out;
        end

        local keyRound = function(key, round)
            local i = (round - 1) * 32;
            local out = key;

            out[33 + i] = XOR(key[ 1 + i], XOR(SBOX[key[30 + i]], RCON[round]));
            out[34 + i] = XOR(key[ 2 + i], SBOX[key[31 + i]]);
            out[35 + i] = XOR(key[ 3 + i], SBOX[key[32 + i]]);
            out[36 + i] = XOR(key[ 4 + i], SBOX[key[29 + i]]);

            out[37 + i] = XOR(out[33 + i], key[ 5 + i]);
            out[38 + i] = XOR(out[34 + i], key[ 6 + i]);
            out[39 + i] = XOR(out[35 + i], key[ 7 + i]);
            out[40 + i] = XOR(out[36 + i], key[ 8 + i]);

            out[41 + i] = XOR(out[37 + i], key[ 9 + i]);
            out[42 + i] = XOR(out[38 + i], key[10 + i]);
            out[43 + i] = XOR(out[39 + i], key[11 + i]);
            out[44 + i] = XOR(out[40 + i], key[12 + i]);

            out[45 + i] = XOR(out[41 + i], key[13 + i]);
            out[46 + i] = XOR(out[42 + i], key[14 + i]);
            out[47 + i] = XOR(out[43 + i], key[15 + i]);
            out[48 + i] = XOR(out[44 + i], key[16 + i]);


            out[49 + i] = XOR(SBOX[out[45 + i]], key[17 + i]);
            out[50 + i] = XOR(SBOX[out[46 + i]], key[18 + i]);
            out[51 + i] = XOR(SBOX[out[47 + i]], key[19 + i]);
            out[52 + i] = XOR(SBOX[out[48 + i]], key[20 + i]);

            out[53 + i] = XOR(out[49 + i], key[21 + i]);
            out[54 + i] = XOR(out[50 + i], key[22 + i]);
            out[55 + i] = XOR(out[51 + i], key[23 + i]);
            out[56 + i] = XOR(out[52 + i], key[24 + i]);

            out[57 + i] = XOR(out[53 + i], key[25 + i]);
            out[58 + i] = XOR(out[54 + i], key[26 + i]);
            out[59 + i] = XOR(out[55 + i], key[27 + i]);
            out[60 + i] = XOR(out[56 + i], key[28 + i]);

            out[61 + i] = XOR(out[57 + i], key[29 + i]);
            out[62 + i] = XOR(out[58 + i], key[30 + i]);
            out[63 + i] = XOR(out[59 + i], key[31 + i]);
            out[64 + i] = XOR(out[60 + i], key[32 + i]);

            return out;
        end

        local keyExpand = function(key)
            local bytes = Array.copy(key);

            for i = 1, 7 do
                keyRound(bytes, i);
            end

            local keys = {};

            keys[ 1] = Array.slice(bytes, 1, 16);
            keys[ 2] = Array.slice(bytes, 17, 32);
            keys[ 3] = Array.slice(bytes, 33, 48);
            keys[ 4] = Array.slice(bytes, 49, 64);
            keys[ 5] = Array.slice(bytes, 65, 80);
            keys[ 6] = Array.slice(bytes, 81, 96);
            keys[ 7] = Array.slice(bytes, 97, 112);
            keys[ 8] = Array.slice(bytes, 113, 128);
            keys[ 9] = Array.slice(bytes, 129, 144);
            keys[10] = Array.slice(bytes, 145, 160);
            keys[11] = Array.slice(bytes, 161, 176);
            keys[12] = Array.slice(bytes, 177, 192);
            keys[13] = Array.slice(bytes, 193, 208);
            keys[14] = Array.slice(bytes, 209, 224);
            keys[15] = Array.slice(bytes, 225, 240);

            return keys;

        end

        local addKey = Array.XOR;

        AES.blockSize = 16;

        AES.encrypt = function(_key, block)

            local key = keyExpand(_key);

            --round 0
            block = addKey(block, key[1]);

            --round 1
            block = byteSub(block, SBOX);
            block = shiftRow(block, ROW_SHIFT);
            block = mixCol(block, MIXTABLE);
            block = addKey(block, key[2]);

            --round 2
            block = byteSub(block, SBOX);
            block = shiftRow(block, ROW_SHIFT);
            block = mixCol(block, MIXTABLE);
            block = addKey(block, key[3]);

            --round 3
            block = byteSub(block, SBOX);
            block = shiftRow(block, ROW_SHIFT);
            block = mixCol(block, MIXTABLE);
            block = addKey(block, key[4]);

            --round 4
            block = byteSub(block, SBOX);
            block = shiftRow(block, ROW_SHIFT);
            block = mixCol(block, MIXTABLE);
            block = addKey(block, key[5]);

            --round 5
            block = byteSub(block, SBOX);
            block = shiftRow(block, ROW_SHIFT);
            block = mixCol(block, MIXTABLE);
            block = addKey(block, key[6]);

            --round 6
            block = byteSub(block, SBOX);
            block = shiftRow(block, ROW_SHIFT);
            block = mixCol(block, MIXTABLE);
            block = addKey(block, key[7]);

            --round 7
            block = byteSub(block, SBOX);
            block = shiftRow(block, ROW_SHIFT);
            block = mixCol(block, MIXTABLE);
            block = addKey(block, key[8]);

            --round 8
            block = byteSub(block, SBOX);
            block = shiftRow(block, ROW_SHIFT);
            block = mixCol(block, MIXTABLE);
            block = addKey(block, key[9]);

            --round 9
            block = byteSub(block, SBOX);
            block = shiftRow(block, ROW_SHIFT);
            block = mixCol(block, MIXTABLE);
            block = addKey(block, key[10]);

            --round 10
            block = byteSub(block, SBOX);
            block = shiftRow(block, ROW_SHIFT);
            block = mixCol(block, MIXTABLE);
            block = addKey(block, key[11]);

            --round 11
            block = byteSub(block, SBOX);
            block = shiftRow(block, ROW_SHIFT);
            block = mixCol(block, MIXTABLE);
            block = addKey(block, key[12]);

            --round 12
            block = byteSub(block, SBOX);
            block = shiftRow(block, ROW_SHIFT);
            block = mixCol(block, MIXTABLE);
            block = addKey(block, key[13]);

            --round 13
            block = byteSub(block, SBOX);
            block = shiftRow(block, ROW_SHIFT);
            block = mixCol(block, MIXTABLE);
            block = addKey(block, key[14]);

            --round 14
            block = byteSub(block, SBOX);
            block = shiftRow(block, ROW_SHIFT);
            block = addKey(block, key[15]);

            return block;

        end

        AES.decrypt = function(_key, block)

            local key = keyExpand(_key);

            --round 0
            block = addKey(block, key[15]);

            --round 1
            block = shiftRow(block, IROW_SHIFT);
            block = byteSub(block, ISBOX);
            block = addKey(block, key[14]);
            block = mixCol(block, IMIXTABLE);

            --round 2
            block = shiftRow(block, IROW_SHIFT);
            block = byteSub(block, ISBOX);
            block = addKey(block, key[13]);
            block = mixCol(block, IMIXTABLE);

            --round 3
            block = shiftRow(block, IROW_SHIFT);
            block = byteSub(block, ISBOX);
            block = addKey(block, key[12]);
            block = mixCol(block, IMIXTABLE);

            --round 4
            block = shiftRow(block, IROW_SHIFT);
            block = byteSub(block, ISBOX);
            block = addKey(block, key[11]);
            block = mixCol(block, IMIXTABLE);

            --round 5
            block = shiftRow(block, IROW_SHIFT);
            block = byteSub(block, ISBOX);
            block = addKey(block, key[10]);
            block = mixCol(block, IMIXTABLE);

            --round 6
            block = shiftRow(block, IROW_SHIFT);
            block = byteSub(block, ISBOX);
            block = addKey(block, key[9]);
            block = mixCol(block, IMIXTABLE);

            --round 7
            block = shiftRow(block, IROW_SHIFT);
            block = byteSub(block, ISBOX);
            block = addKey(block, key[8]);
            block = mixCol(block, IMIXTABLE);

            --round 8
            block = shiftRow(block, IROW_SHIFT);
            block = byteSub(block, ISBOX);
            block = addKey(block, key[7]);
            block = mixCol(block, IMIXTABLE);

            --round 9
            block = shiftRow(block, IROW_SHIFT);
            block = byteSub(block, ISBOX);
            block = addKey(block, key[6]);
            block = mixCol(block, IMIXTABLE);

            --round 10
            block = shiftRow(block, IROW_SHIFT);
            block = byteSub(block, ISBOX);
            block = addKey(block, key[5]);
            block = mixCol(block, IMIXTABLE);

            --round 11
            block = shiftRow(block, IROW_SHIFT);
            block = byteSub(block, ISBOX);
            block = addKey(block, key[4]);
            block = mixCol(block, IMIXTABLE);

            --round 12
            block = shiftRow(block, IROW_SHIFT);
            block = byteSub(block, ISBOX);
            block = addKey(block, key[3]);
            block = mixCol(block, IMIXTABLE);

            --round 13
            block = shiftRow(block, IROW_SHIFT);
            block = byteSub(block, ISBOX);
            block = addKey(block, key[2]);
            block = mixCol(block, IMIXTABLE);

            --round 14
            block = shiftRow(block, IROW_SHIFT);
            block = byteSub(block, ISBOX);
            block = addKey(block, key[1]);

            return block;
        end
    end

    local CBC = {}; do
        CBC.Cipher = function()

            local public = {};

            local key;
            local blockCipher;
            local padding;
            local inputQueue;
            local outputQueue;
            local iv;

            public.setKey = function(keyBytes)
                key = keyBytes;
                return public;
            end

            public.setBlockCipher = function(cipher)
                blockCipher = cipher;
                return public;
            end

            public.setPadding = function(paddingMode)
                padding = paddingMode;
                return public;
            end

            public.init = function()
                inputQueue = Queue();
                outputQueue = Queue();
                iv = nil;
                return public;
            end

            public.update = function(messageStream)
                local byte = messageStream();
                while (byte ~= nil) do
                    inputQueue.push(byte);
                    if(inputQueue.size() >= blockCipher.blockSize) then
                        local block = Array.readFromQueue(inputQueue, blockCipher.blockSize);

                        if(iv == nil) then
                            iv = block;
                        else
                            local out = Array.XOR(iv, block);
                            out = blockCipher.encrypt(key, out);
                            Array.writeToQueue(outputQueue, out);
                            iv = out;
                        end
                    end
                    byte = messageStream();
                end
                return public;
            end

            public.finish = function()
                local paddingStream = padding(blockCipher.blockSize, inputQueue.getHead());
                public.update(paddingStream);

                return public;
            end

            public.getOutputQueue = function()
                return outputQueue;
            end

            public.asHex = function()
                return Stream.toHex(outputQueue.pop);
            end

            public.asBytes = function()
                return Stream.toArray(outputQueue.pop);
            end

            return public;

        end

        CBC.Decipher = function()

            local public = {};

            local key;
            local blockCipher;
            local padding;
            local inputQueue;
            local outputQueue;
            local iv;

            public.setKey = function(keyBytes)
                key = keyBytes;
                return public;
            end

            public.setBlockCipher = function(cipher)
                blockCipher = cipher;
                return public;
            end

            public.setPadding = function(paddingMode)
                padding = paddingMode;
                return public;
            end

            public.init = function()
                inputQueue = Queue();
                outputQueue = Queue();
                iv = nil;
                return public;
            end

            public.update = function(messageStream)
                local byte = messageStream();
                while (byte ~= nil) do
                    inputQueue.push(byte);
                    if(inputQueue.size() >= blockCipher.blockSize) then
                        local block = Array.readFromQueue(inputQueue, blockCipher.blockSize);

                        if(iv == nil) then
                            iv = block;
                        else
                            local out = block;
                            out = blockCipher.decrypt(key, out);
                            out = Array.XOR(iv, out);
                            Array.writeToQueue(outputQueue, out);
                            iv = block;
                        end
                    end
                    byte = messageStream();
                end
                return public;
            end

            public.finish = function()
                local paddingStream = padding(blockCipher.blockSize, inputQueue.getHead());
                public.update(paddingStream);

                return public;
            end

            public.getOutputQueue = function()
                return outputQueue;
            end

            public.asHex = function()
                return Stream.toHex(outputQueue.pop);
            end

            public.asBytes = function()
                return Stream.toArray(outputQueue.pop);
            end

            return public;

        end
    end

  local ZeroPadding = function(blockSize, byteCount)

    local paddingCount = blockSize - ((byteCount -1) % blockSize) + 1;
    local bytesLeft = paddingCount;

    local stream = function()
        if bytesLeft > 0 then
            bytesLeft = bytesLeft - 1;
            return 0x00;
        else
            return nil;
        end
    end

    return stream;
  end

  local PadCharacter = "#" --SOMETHING THAT WONT APPEAR INSIDE YOUR PLAINTEXT TEXT
  local function HexPad(s)
    while #s*2%32 ~= 0 do s=s..PadCharacter end
    return (s:gsub(".", function(char) return string.format("%2x", char:byte()) end))
  end

  local function HexUnpad(s)
    s = (s:gsub("%x%x", function(digits) return string.char(tonumber(digits, 16)) end))
    return s:gsub(PadCharacter, "")
  end

  function crypt.encrypt(stringkey, stringiv, stringplaintext)
    local plaintext = Stream.fromArray(Array.fromHex(HexPad(stringplaintext)))

    print("Plaintext", HexPad(stringplaintext))

    local cipher = CBC.Cipher()
      .setKey(Array.fromHex(stringkey))
      .setBlockCipher(AES)
      .setPadding(ZeroPadding)

    return cipher
      .init()
      .update(Stream.fromArray(Array.fromHex(stringiv)))
      .update(plaintext)
      .finish()
      .asHex()
  end

  function crypt.decrypt(stringkey, stringiv, ciphertext)
    local decipher = CBC.Decipher()
      .setKey(Array.fromHex(stringkey))
      .setBlockCipher(AES)
      .setPadding(ZeroPadding)

    return HexUnpad(decipher
      .init()
      .update(Stream.fromArray(Array.fromHex(stringiv)))
      .update(Stream.fromHex(ciphertext))
      .finish()
      .asHex())
  end
end

local key = "603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4" --Key, 64 hex charcaters
local iv = "000102030405060708090A0B0C0D0E0F" -- Initialisation vector, 32 characters
local plaintext = "6bc1bee22e409f96e93d7e117393172a" -- Plain text to encrypt, any length

local encrypted = crypt.encrypt(key, iv, plaintext)
local decrypted = crypt.decrypt(key, iv, encrypted)
print("Encrypted:", #encrypted, encrypted)
print("Decrypted:", #decrypted, decrypted)
