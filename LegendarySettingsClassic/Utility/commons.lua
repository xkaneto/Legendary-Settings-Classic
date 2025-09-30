local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
    return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
    local DIP = 1;
    local repeatNext;
    ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
        if (Byte(byte, 2) == 81) then
            repeatNext = StrToNumber(Sub(byte, 1, 1));
            return "";
        else
            local a = Char(StrToNumber(byte, 16));
            if repeatNext then
                local b = Rep(a, repeatNext);
                repeatNext = nil;
                return b;
            else
                return a;
            end
        end
    end);
    local function gBit(Bit, Start, End)
        if End then
            local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
            return Res - (Res % 1);
        else
            local Plc = 2 ^ (Start - 1);
            return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
        end
    end
    local function gBits8()
        local a = Byte(ByteString, DIP, DIP);
        DIP = DIP + 1;
        return a;
    end
    local function gBits16()
        local a, b = Byte(ByteString, DIP, DIP + 2);
        DIP = DIP + 2;
        return (b * 256) + a;
    end
    local function gBits32()
        local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
        DIP = DIP + 4;
        return (d * 16777216) + (c * 65536) + (b * 256) + a;
    end
    local function gFloat()
        local Left = gBits32();
        local Right = gBits32();
        local IsNormal = 1;
        local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
        local Exponent = gBit(Right, 21, 31);
        local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
        if (Exponent == 0) then
            if (Mantissa == 0) then
                return Sign * 0;
            else
                Exponent = 1;
                IsNormal = 0;
            end
        elseif (Exponent == 2047) then
            return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
        end
        return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
    end
    local function gString(Len)
        local Str;
        if not Len then
            Len = gBits32();
            if (Len == 0) then
                return "";
            end
        end
        Str = Sub(ByteString, DIP, (DIP + Len) - 1);
        DIP = DIP + Len;
        local FStr = {};
        for Idx = 1, #Str do
            FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
        end
        return Concat(FStr);
    end
    local gInt = gBits32;
    local function _R(...)
        return {...}, Select("#", ...);
    end
    local function Deserialize()
        local Instrs = {};
        local Functions = {};
        local Lines = {};
        local Chunk = {Instrs, Functions, nil, Lines};
        local ConstCount = gBits32();
        local Consts = {};
        for Idx = 1, ConstCount do
            local Type = gBits8();
            local Cons;
            if (Type == 1) then
                Cons = gBits8() ~= 0;
            elseif (Type == 2) then
                Cons = gFloat();
            elseif (Type == 3) then
                Cons = gString();
            end
            Consts[Idx] = Cons;
        end
        Chunk[3] = gBits8();
        for Idx = 1, gBits32() do
            local Descriptor = gBits8();
            if (gBit(Descriptor, 1, 1) == 0) then
                local Type = gBit(Descriptor, 2, 3);
                local Mask = gBit(Descriptor, 4, 6);
                local Inst = {gBits16(), gBits16(), nil, nil};
                if (Type == 0) then
                    Inst[3] = gBits16();
                    Inst[4] = gBits16();
                elseif (Type == 1) then
                    Inst[3] = gBits32();
                elseif (Type == 2) then
                    Inst[3] = gBits32() - (2 ^ 16);
                elseif (Type == 3) then
                    Inst[3] = gBits32() - (2 ^ 16);
                    Inst[4] = gBits16();
                end
                if (gBit(Mask, 1, 1) == 1) then
                    Inst[2] = Consts[Inst[2]];
                end
                if (gBit(Mask, 2, 2) == 1) then
                    Inst[3] = Consts[Inst[3]];
                end
                if (gBit(Mask, 3, 3) == 1) then
                    Inst[4] = Consts[Inst[4]];
                end
                Instrs[Idx] = Inst;
            end
        end
        for Idx = 1, gBits32() do
            Functions[Idx - 1] = Deserialize();
        end
        return Chunk;
    end
    local function Wrap(Chunk, Upvalues, Env)
        local Instr = Chunk[1];
        local Proto = Chunk[2];
        local Params = Chunk[3];
        return function(...)
            local Instr = Instr;
            local Proto = Proto;
            local Params = Params;
            local _R = _R;
            local VIP = 1;
            local Top = -1;
            local Vararg = {};
            local Args = {...};
            local PCount = Select("#", ...) - 1;
            local Lupvals = {};
            local Stk = {};
            for Idx = 0, PCount do
                if (Idx >= Params) then
                    Vararg[Idx - Params] = Args[Idx + 1];
                else
                    Stk[Idx] = Args[Idx + 1];
                end
            end
            local Varargsz = (PCount - Params) + 1;
            local Inst;
            local Enum;
            while true do
                Inst = Instr[VIP];
                Enum = Inst[1];
                if (Enum <= 145) then
                    if (Enum <= 72) then
                        if (Enum <= 35) then
                            if (Enum <= 17) then
                                if (Enum <= 8) then
                                    if (Enum <= 3) then
                                        if (Enum <= 1) then
                                            if (Enum == 0) then
                                                if (Stk[Inst[2]] > Stk[Inst[4]]) then
                                                    VIP = VIP + 1;
                                                else
                                                    VIP = VIP + Inst[3];
                                                end
                                            else
                                                local A = Inst[2];
                                                Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                            end
                                        elseif (Enum == 2) then
                                            local A;
                                            Stk[Inst[2]] = Env[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            A = Inst[2];
                                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            if not Stk[Inst[2]] then
                                                VIP = VIP + 1;
                                            else
                                                VIP = Inst[3];
                                            end
                                        else
                                            local A;
                                            A = Inst[2];
                                            Stk[A] = Stk[A]();
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            do
                                                return Stk[Inst[2]];
                                            end
                                        end
                                    elseif (Enum <= 5) then
                                        if (Enum > 4) then
                                            local A;
                                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Upvalues[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            A = Inst[2];
                                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            if (Stk[Inst[2]] ~= Inst[4]) then
                                                VIP = VIP + 1;
                                            else
                                                VIP = Inst[3];
                                            end
                                        else
                                            local A;
                                            Stk[Inst[2]] = Upvalues[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            A = Inst[2];
                                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                                VIP = VIP + 1;
                                            else
                                                VIP = Inst[3];
                                            end
                                        end
                                    elseif (Enum <= 6) then
                                        Stk[Inst[2]] = Inst[3];
                                    elseif (Enum == 7) then
                                        local B;
                                        local A;
                                        A = Inst[2];
                                        B = Inst[3];
                                        for Idx = A, B do
                                            Stk[Idx] = Vararg[Idx - A];
                                        end
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = {};
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = {};
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = {};
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                    else
                                        local A;
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        VIP = Inst[3];
                                    end
                                elseif (Enum <= 12) then
                                    if (Enum <= 10) then
                                        if (Enum > 9) then
                                            local Edx;
                                            local Results;
                                            local B;
                                            local A;
                                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            A = Inst[2];
                                            B = Stk[Inst[3]];
                                            Stk[A + 1] = B;
                                            Stk[A] = B[Inst[4]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            A = Inst[2];
                                            Results = {Stk[A](Stk[A + 1])};
                                            Edx = 0;
                                            for Idx = A, Inst[4] do
                                                Edx = Edx + 1;
                                                Stk[Idx] = Results[Edx];
                                            end
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            if (Stk[Inst[2]] < Inst[4]) then
                                                VIP = VIP + 1;
                                            else
                                                VIP = Inst[3];
                                            end
                                        else
                                            local Edx;
                                            local Results, Limit;
                                            local A;
                                            Stk[Inst[2]] = Env[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Upvalues[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            A = Inst[2];
                                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                            Top = (Limit + A) - 1;
                                            Edx = 0;
                                            for Idx = A, Top do
                                                Edx = Edx + 1;
                                                Stk[Idx] = Results[Edx];
                                            end
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            A = Inst[2];
                                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
                                            Top = (Limit + A) - 1;
                                            Edx = 0;
                                            for Idx = A, Top do
                                                Edx = Edx + 1;
                                                Stk[Idx] = Results[Edx];
                                            end
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            A = Inst[2];
                                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            if Stk[Inst[2]] then
                                                VIP = VIP + 1;
                                            else
                                                VIP = Inst[3];
                                            end
                                        end
                                    elseif (Enum == 11) then
                                        local B;
                                        local A;
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        B = Stk[Inst[4]];
                                        if not B then
                                            VIP = VIP + 1;
                                        else
                                            Stk[Inst[2]] = B;
                                            VIP = Inst[3];
                                        end
                                    else
                                        local A;
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3] ~= 0;
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3] ~= 0;
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3] ~= 0;
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3] ~= 0;
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3] ~= 0;
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3] ~= 0;
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3] ~= 0;
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3] ~= 0;
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3] ~= 0;
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    end
                                elseif (Enum <= 14) then
                                    if (Enum > 13) then
                                        local Edx;
                                        local Results, Limit;
                                        local B;
                                        local A;
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        B = Stk[Inst[3]];
                                        Stk[A + 1] = B;
                                        Stk[A] = B[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                        Top = (Limit + A) - 1;
                                        Edx = 0;
                                        for Idx = A, Top do
                                            Edx = Edx + 1;
                                            Stk[Idx] = Results[Edx];
                                        end
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A](Unpack(Stk, A + 1, Top));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        B = Stk[Inst[3]];
                                        Stk[A + 1] = B;
                                        Stk[A] = B[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                        Top = (Limit + A) - 1;
                                        Edx = 0;
                                        for Idx = A, Top do
                                            Edx = Edx + 1;
                                            Stk[Idx] = Results[Edx];
                                        end
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A](Unpack(Stk, A + 1, Top));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                    else
                                        local A = Inst[2];
                                        Top = (A + Varargsz) - 1;
                                        for Idx = A, Top do
                                            local VA = Vararg[Idx - A];
                                            Stk[Idx] = VA;
                                        end
                                    end
                                elseif (Enum <= 15) then
                                    Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
                                elseif (Enum == 16) then
                                    local A;
                                    A = Inst[2];
                                    Stk[A] = Stk[A]();
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    VIP = Inst[3];
                                else
                                    local A = Inst[2];
                                    local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    local Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                end
                            elseif (Enum <= 26) then
                                if (Enum <= 21) then
                                    if (Enum <= 19) then
                                        if (Enum > 18) then
                                            local A;
                                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            A = Inst[2];
                                            Stk[A] = Stk[A](Stk[A + 1]);
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Upvalues[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            A = Inst[2];
                                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                                VIP = VIP + 1;
                                            else
                                                VIP = Inst[3];
                                            end
                                        else
                                            local A;
                                            Stk[Inst[2]] = Upvalues[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            A = Inst[2];
                                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Env[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            if Stk[Inst[2]] then
                                                VIP = VIP + 1;
                                            else
                                                VIP = Inst[3];
                                            end
                                        end
                                    elseif (Enum == 20) then
                                        Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
                                    else
                                        local A;
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Stk[A + 1]);
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    end
                                elseif (Enum <= 23) then
                                    if (Enum == 22) then
                                        local A;
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                    else
                                        local A;
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    end
                                elseif (Enum <= 24) then
                                    local B;
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    B = Stk[Inst[3]];
                                    Stk[A + 1] = B;
                                    Stk[A] = B[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                elseif (Enum == 25) then
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = {};
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A]();
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    VIP = Inst[3];
                                else
                                    local Edx;
                                    local Results, Limit;
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 30) then
                                if (Enum <= 28) then
                                    if (Enum == 27) then
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Inst[3]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Inst[3]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                    else
                                        Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
                                    end
                                elseif (Enum == 29) then
                                    local A;
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    local A;
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                end
                            elseif (Enum <= 32) then
                                if (Enum == 31) then
                                    Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
                                else
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3] ~= 0;
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 33) then
                                local Edx;
                                local Results, Limit;
                                local B;
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                B = Stk[Inst[3]];
                                Stk[A + 1] = B;
                                Stk[A] = B[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                B = Stk[Inst[3]];
                                Stk[A + 1] = B;
                                Stk[A] = B[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                            elseif (Enum > 34) then
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Stk[A + 1]);
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                do
                                    return Stk[Inst[2]];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                VIP = Inst[3];
                            else
                                local A;
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Upvalues[Inst[3]] = Stk[Inst[2]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                VIP = Inst[3];
                            end
                        elseif (Enum <= 53) then
                            if (Enum <= 44) then
                                if (Enum <= 39) then
                                    if (Enum <= 37) then
                                        if (Enum > 36) then
                                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            VIP = Inst[3];
                                        elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    elseif (Enum == 38) then
                                        Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                    else
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        VIP = Inst[3];
                                    end
                                elseif (Enum <= 41) then
                                    if (Enum == 40) then
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if not Stk[Inst[2]] then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    elseif (Stk[Inst[2]] > Inst[4]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                elseif (Enum <= 42) then
                                    local A;
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] ~= Inst[4]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                elseif (Enum > 43) then
                                    if (Inst[2] == Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if not Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 48) then
                                if (Enum <= 46) then
                                    if (Enum == 45) then
                                        local A = Inst[2];
                                        do
                                            return Unpack(Stk, A, A + Inst[3]);
                                        end
                                    else
                                        local Edx;
                                        local Results, Limit;
                                        local A;
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                        Top = (Limit + A) - 1;
                                        Edx = 0;
                                        for Idx = A, Top do
                                            Edx = Edx + 1;
                                            Stk[Idx] = Results[Edx];
                                        end
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        for Idx = Inst[2], Inst[3] do
                                            Stk[Idx] = nil;
                                        end
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    end
                                elseif (Enum == 47) then
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if not Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    local A;
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 50) then
                                if (Enum > 49) then
                                    local A;
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    local Results, Limit;
                                    local Edx;
                                    local Limit;
                                    local Results;
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results = {Stk[A]()};
                                    Limit = Inst[4];
                                    Edx = 0;
                                    for Idx = A, Limit do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                                    Edx = 0;
                                    for Idx = A, Inst[4] do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                                    Edx = 0;
                                    for Idx = A, Inst[4] do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                                    Edx = 0;
                                    for Idx = A, Inst[4] do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 51) then
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                            elseif (Enum > 52) then
                                local A;
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] > Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = VIP + Inst[3];
                                end
                            end
                        elseif (Enum <= 62) then
                            if (Enum <= 57) then
                                if (Enum <= 55) then
                                    if (Enum > 54) then
                                        local A;
                                        Stk[Inst[2]] = {};
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    else
                                        local A;
                                        Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Stk[A + 1]);
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3] ~= 0;
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    end
                                elseif (Enum > 56) then
                                    if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    local VA;
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Top = (A + Varargsz) - 1;
                                    for Idx = A, Top do
                                        VA = Vararg[Idx - A];
                                        Stk[Idx] = VA;
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    do
                                        return Stk[A](Unpack(Stk, A + 1, Top));
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    do
                                        return Unpack(Stk, A, Top);
                                    end
                                end
                            elseif (Enum <= 59) then
                                if (Enum > 58) then
                                    local Results;
                                    local Edx;
                                    local Results, Limit;
                                    local A;
                                    Stk[Inst[2]]();
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]]();
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]]();
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]]();
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                                    Edx = 0;
                                    for Idx = A, Inst[4] do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                elseif (Stk[Inst[2]] < Inst[4]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            elseif (Enum <= 60) then
                                local A;
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            elseif (Enum > 61) then
                                local A = Inst[2];
                                local Step = Stk[A + 2];
                                local Index = Stk[A] + Step;
                                Stk[A] = Index;
                                if (Step > 0) then
                                    if (Index <= Stk[A + 1]) then
                                        VIP = Inst[3];
                                        Stk[A + 3] = Index;
                                    end
                                elseif (Index >= Stk[A + 1]) then
                                    VIP = Inst[3];
                                    Stk[A + 3] = Index;
                                end
                            else
                                local A;
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Upvalues[Inst[3]] = Stk[Inst[2]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Upvalues[Inst[3]] = Stk[Inst[2]];
                            end
                        elseif (Enum <= 67) then
                            if (Enum <= 64) then
                                if (Enum > 63) then
                                    if (Stk[Inst[2]] < Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    local A;
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Stk[A + 1]);
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Stk[A + 1]);
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 65) then
                                local A = Inst[2];
                                do
                                    return Unpack(Stk, A, Top);
                                end
                            elseif (Enum == 66) then
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                VIP = Inst[3];
                            end
                        elseif (Enum <= 69) then
                            if (Enum == 68) then
                                local A;
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] > Inst[4]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                local A;
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 70) then
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            VIP = Inst[3];
                        elseif (Enum > 71) then
                            local A;
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        else
                            local Edx;
                            local Results;
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results = {Stk[A](Stk[A + 1])};
                            Edx = 0;
                            for Idx = A, Inst[4] do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            VIP = Inst[3];
                        end
                    elseif (Enum <= 108) then
                        if (Enum <= 90) then
                            if (Enum <= 81) then
                                if (Enum <= 76) then
                                    if (Enum <= 74) then
                                        if (Enum > 73) then
                                            local A;
                                            A = Inst[2];
                                            Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Env[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]][Inst[3]] = Inst[4];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            VIP = Inst[3];
                                        else
                                            Stk[Inst[2]] = Env[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Env[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            if not Stk[Inst[2]] then
                                                VIP = VIP + 1;
                                            else
                                                VIP = Inst[3];
                                            end
                                        end
                                    elseif (Enum > 75) then
                                        local A;
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A]();
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Stk[A + 1]);
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if Stk[Inst[2]] then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    else
                                        local A;
                                        Stk[Inst[2]] = {};
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                    end
                                elseif (Enum <= 78) then
                                    if (Enum > 77) then
                                        if (Stk[Inst[2]] ~= Inst[4]) then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    elseif (Stk[Inst[2]] <= Inst[4]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                elseif (Enum <= 79) then
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                elseif (Enum == 80) then
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                else
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Stk[A + 1]);
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    VIP = Inst[3];
                                end
                            elseif (Enum <= 85) then
                                if (Enum <= 83) then
                                    if (Enum == 82) then
                                        local Results;
                                        local Edx;
                                        local Results, Limit;
                                        local A;
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                        Top = (Limit + A) - 1;
                                        Edx = 0;
                                        for Idx = A, Top do
                                            Edx = Edx + 1;
                                            Stk[Idx] = Results[Edx];
                                        end
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                                        Edx = 0;
                                        for Idx = A, Inst[4] do
                                            Edx = Edx + 1;
                                            Stk[Idx] = Results[Edx];
                                        end
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if Stk[Inst[2]] then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    else
                                        local A;
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    end
                                elseif (Enum > 84) then
                                    Stk[Inst[2]] = Env[Inst[3]];
                                else
                                    local B;
                                    local A;
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    B = Stk[Inst[4]];
                                    if B then
                                        VIP = VIP + 1;
                                    else
                                        Stk[Inst[2]] = B;
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 87) then
                                if (Enum == 86) then
                                    local B;
                                    local Edx;
                                    local Results, Limit;
                                    local A;
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A](Unpack(Stk, A + 1, Top));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    B = Stk[Inst[3]];
                                    Stk[A + 1] = B;
                                    Stk[A] = B[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                else
                                    local A;
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] <= Inst[4]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 88) then
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            elseif (Enum == 89) then
                                local Edx;
                                local Results;
                                local A;
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results = {Stk[A](Stk[A + 1])};
                                Edx = 0;
                                for Idx = A, Inst[4] do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                local B;
                                local A;
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                B = Stk[Inst[4]];
                                if B then
                                    VIP = VIP + 1;
                                else
                                    Stk[Inst[2]] = B;
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 99) then
                            if (Enum <= 94) then
                                if (Enum <= 92) then
                                    if (Enum == 91) then
                                        local Edx;
                                        local Results, Limit;
                                        local A;
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                        Top = (Limit + A) - 1;
                                        Edx = 0;
                                        for Idx = A, Top do
                                            Edx = Edx + 1;
                                            Stk[Idx] = Results[Edx];
                                        end
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                    else
                                        local A;
                                        Stk[Inst[2]] = {};
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if Stk[Inst[2]] then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    end
                                elseif (Enum > 93) then
                                    Env[Inst[3]] = Stk[Inst[2]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if not Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    local A;
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 96) then
                                if (Enum > 95) then
                                    local A;
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                else
                                    local Step;
                                    local Index;
                                    local A;
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Stk[A + 1]);
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Index = Stk[A];
                                    Step = Stk[A + 2];
                                    if (Step > 0) then
                                        if (Index > Stk[A + 1]) then
                                            VIP = Inst[3];
                                        else
                                            Stk[A + 3] = Index;
                                        end
                                    elseif (Index < Stk[A + 1]) then
                                        VIP = Inst[3];
                                    else
                                        Stk[A + 3] = Index;
                                    end
                                end
                            elseif (Enum <= 97) then
                                local A;
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            elseif (Enum == 98) then
                                local A;
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                local A = Inst[2];
                                local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
                                Top = (Limit + A) - 1;
                                local Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                            end
                        elseif (Enum <= 103) then
                            if (Enum <= 101) then
                                if (Enum == 100) then
                                    local Edx;
                                    local Results, Limit;
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                else
                                    Stk[Inst[2]]();
                                end
                            elseif (Enum > 102) then
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                            else
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 105) then
                            if (Enum == 104) then
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                VIP = Inst[3];
                            else
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 106) then
                            local B;
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            B = Stk[Inst[4]];
                            if not B then
                                VIP = VIP + 1;
                            else
                                Stk[Inst[2]] = B;
                                VIP = Inst[3];
                            end
                        elseif (Enum == 107) then
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            for Idx = Inst[2], Inst[3] do
                                Stk[Idx] = nil;
                            end
                        elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
                            VIP = Inst[3];
                        else
                            VIP = VIP + 1;
                        end
                    elseif (Enum <= 126) then
                        if (Enum <= 117) then
                            if (Enum <= 112) then
                                if (Enum <= 110) then
                                    if (Enum == 109) then
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Upvalues[Inst[3]] = Stk[Inst[2]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if (Stk[Inst[2]] <= Stk[Inst[4]]) then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    else
                                        local Edx;
                                        local Results, Limit;
                                        local B;
                                        local A;
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        B = Stk[Inst[3]];
                                        Stk[A + 1] = B;
                                        Stk[A] = B[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Results, Limit = _R(Stk[A](Stk[A + 1]));
                                        Top = (Limit + A) - 1;
                                        Edx = 0;
                                        for Idx = A, Top do
                                            Edx = Edx + 1;
                                            Stk[Idx] = Results[Edx];
                                        end
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        B = Stk[Inst[3]];
                                        Stk[A + 1] = B;
                                        Stk[A] = B[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Results, Limit = _R(Stk[A](Stk[A + 1]));
                                        Top = (Limit + A) - 1;
                                        Edx = 0;
                                        for Idx = A, Top do
                                            Edx = Edx + 1;
                                            Stk[Idx] = Results[Edx];
                                        end
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        VIP = Inst[3];
                                    end
                                elseif (Enum > 111) then
                                    local A = Inst[2];
                                    local Results, Limit = _R(Stk[A](Stk[A + 1]));
                                    Top = (Limit + A) - 1;
                                    local Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                else
                                    local A;
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Upvalues[Inst[3]] = Stk[Inst[2]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Upvalues[Inst[3]] = Stk[Inst[2]];
                                end
                            elseif (Enum <= 114) then
                                if (Enum > 113) then
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if not Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    local A;
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Stk[A + 1]);
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 115) then
                                local Edx;
                                local Results, Limit;
                                local B;
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                B = Stk[Inst[3]];
                                Stk[A + 1] = B;
                                Stk[A] = B[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                B = Stk[Inst[3]];
                                Stk[A + 1] = B;
                                Stk[A] = B[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                VIP = Inst[3];
                            elseif (Enum > 116) then
                                local A;
                                local K;
                                local B;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                B = Inst[3];
                                K = Stk[B];
                                for Idx = B + 1, Inst[4] do
                                    K = K .. Stk[Idx];
                                end
                                Stk[Inst[2]] = K;
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Stk[A + 1]);
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                for Idx = Inst[2], Inst[3] do
                                    Stk[Idx] = nil;
                                end
                            end
                        elseif (Enum <= 121) then
                            if (Enum <= 119) then
                                if (Enum > 118) then
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Stk[A + 1]);
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    local A;
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum == 120) then
                                local DIP;
                                local NStk;
                                local Upv;
                                local List;
                                local Cls;
                                local Edx;
                                local Results, Limit;
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Upvalues[Inst[3]] = Stk[Inst[2]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Cls = {};
                                for Idx = 1, #Lupvals do
                                    List = Lupvals[Idx];
                                    for Idz = 0, #List do
                                        Upv = List[Idz];
                                        NStk = Upv[1];
                                        DIP = Upv[2];
                                        if ((NStk == Stk) and (DIP >= A)) then
                                            Cls[DIP] = NStk[DIP];
                                            Upv[1] = Cls;
                                        end
                                    end
                                end
                            else
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = {};
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                VIP = Inst[3];
                            end
                        elseif (Enum <= 123) then
                            if (Enum == 122) then
                                local K;
                                local B;
                                local A;
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                B = Inst[3];
                                K = Stk[B];
                                for Idx = B + 1, Inst[4] do
                                    K = K .. Stk[Idx];
                                end
                                Stk[Inst[2]] = K;
                            else
                                local B;
                                local Edx;
                                local Results, Limit;
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                B = Stk[Inst[4]];
                                if not B then
                                    VIP = VIP + 1;
                                else
                                    Stk[Inst[2]] = B;
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 124) then
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = {};
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A]();
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = #Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                        elseif (Enum == 125) then
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            VIP = Inst[3];
                        else
                            Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
                        end
                    elseif (Enum <= 135) then
                        if (Enum <= 130) then
                            if (Enum <= 128) then
                                if (Enum > 127) then
                                    local A;
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                else
                                    local Edx;
                                    local Results;
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results = {Stk[A](Stk[A + 1])};
                                    Edx = 0;
                                    for Idx = A, Inst[4] do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] == Inst[4]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum == 129) then
                                local Results;
                                local Edx;
                                local Results, Limit;
                                local A;
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                                Edx = 0;
                                for Idx = A, Inst[4] do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                local A = Inst[2];
                                local Results = {Stk[A]()};
                                local Limit = Inst[4];
                                local Edx = 0;
                                for Idx = A, Limit do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                            end
                        elseif (Enum <= 132) then
                            if (Enum == 131) then
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                local Edx;
                                local Results;
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results = {Stk[A](Stk[A + 1])};
                                Edx = 0;
                                for Idx = A, Inst[4] do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Stk[A + 1]);
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 133) then
                            local A;
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        elseif (Enum == 134) then
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            VIP = Inst[3];
                        else
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            VIP = Inst[3];
                        end
                    elseif (Enum <= 140) then
                        if (Enum <= 137) then
                            if (Enum > 136) then
                                if Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] == Inst[4]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 138) then
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A]();
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        elseif (Enum > 139) then
                            Stk[Inst[2]] = #Stk[Inst[3]];
                        else
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        end
                    elseif (Enum <= 142) then
                        if (Enum > 141) then
                            if (Stk[Inst[2]] == Inst[4]) then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        else
                            Stk[Inst[2]] = not Stk[Inst[3]];
                        end
                    elseif (Enum <= 143) then
                        local A;
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        if Stk[Inst[2]] then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    elseif (Enum == 144) then
                        local A;
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Stk[A + 1]);
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        if (Stk[Inst[2]] == Stk[Inst[4]]) then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    else
                        local Edx;
                        local Results;
                        local A;
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
                        Edx = 0;
                        for Idx = A, Inst[4] do
                            Edx = Edx + 1;
                            Stk[Idx] = Results[Edx];
                        end
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        if not Stk[Inst[2]] then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    end
                elseif (Enum <= 218) then
                    if (Enum <= 181) then
                        if (Enum <= 163) then
                            if (Enum <= 154) then
                                if (Enum <= 149) then
                                    if (Enum <= 147) then
                                        if (Enum > 146) then
                                            local A;
                                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            A = Inst[2];
                                            Stk[A] = Stk[A](Stk[A + 1]);
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Upvalues[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            A = Inst[2];
                                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                                VIP = VIP + 1;
                                            else
                                                VIP = Inst[3];
                                            end
                                        else
                                            Stk[Inst[2]] = {};
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Env[Inst[3]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Inst[3];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                            VIP = VIP + 1;
                                            Inst = Instr[VIP];
                                            if not Stk[Inst[2]] then
                                                VIP = VIP + 1;
                                            else
                                                VIP = Inst[3];
                                            end
                                        end
                                    elseif (Enum == 148) then
                                        local A;
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    else
                                        local A;
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if Stk[Inst[2]] then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    end
                                elseif (Enum <= 151) then
                                    if (Enum == 150) then
                                        local A = Inst[2];
                                        do
                                            return Stk[A](Unpack(Stk, A + 1, Top));
                                        end
                                    else
                                        local A;
                                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A]();
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if (Stk[Inst[2]] == Inst[4]) then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    end
                                elseif (Enum <= 152) then
                                    local A;
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                elseif (Enum > 153) then
                                    local A = Inst[2];
                                    Stk[A](Stk[A + 1]);
                                else
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                end
                            elseif (Enum <= 158) then
                                if (Enum <= 156) then
                                    if (Enum > 155) then
                                        local A = Inst[2];
                                        local C = Inst[4];
                                        local CB = A + 2;
                                        local Result = {Stk[A](Stk[A + 1], Stk[CB])};
                                        for Idx = 1, C do
                                            Stk[CB + Idx] = Result[Idx];
                                        end
                                        local R = Result[1];
                                        if R then
                                            Stk[CB] = R;
                                            VIP = Inst[3];
                                        else
                                            VIP = VIP + 1;
                                        end
                                    elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                elseif (Enum > 157) then
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    VIP = Inst[3];
                                else
                                    local A = Inst[2];
                                    local T = Stk[A];
                                    for Idx = A + 1, Top do
                                        Insert(T, Stk[Idx]);
                                    end
                                end
                            elseif (Enum <= 160) then
                                if (Enum == 159) then
                                    local Step;
                                    local Index;
                                    local A;
                                    Stk[Inst[2]] = {};
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = #Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Index = Stk[A];
                                    Step = Stk[A + 2];
                                    if (Step > 0) then
                                        if (Index > Stk[A + 1]) then
                                            VIP = Inst[3];
                                        else
                                            Stk[A + 3] = Index;
                                        end
                                    elseif (Index < Stk[A + 1]) then
                                        VIP = Inst[3];
                                    else
                                        Stk[A + 3] = Index;
                                    end
                                else
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                end
                            elseif (Enum <= 161) then
                                local Edx;
                                local Results, Limit;
                                local B;
                                local A;
                                A = Inst[2];
                                B = Stk[Inst[3]];
                                Stk[A + 1] = B;
                                Stk[A] = B[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                VIP = Inst[3];
                            elseif (Enum > 162) then
                                local A;
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] > Inst[4]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            end
                        elseif (Enum <= 172) then
                            if (Enum <= 167) then
                                if (Enum <= 165) then
                                    if (Enum > 164) then
                                        local A;
                                        Stk[Inst[2]] = Upvalues[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    else
                                        local Edx;
                                        local Results;
                                        local A;
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Results = {Stk[A](Stk[A + 1])};
                                        Edx = 0;
                                        for Idx = A, Inst[4] do
                                            Edx = Edx + 1;
                                            Stk[Idx] = Results[Edx];
                                        end
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        if (Stk[Inst[2]] == Inst[4]) then
                                            VIP = VIP + 1;
                                        else
                                            VIP = Inst[3];
                                        end
                                    end
                                elseif (Enum == 166) then
                                    local A = Inst[2];
                                    local Results = {Stk[A](Stk[A + 1])};
                                    local Edx = 0;
                                    for Idx = A, Inst[4] do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                else
                                    local A;
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 169) then
                                if (Enum == 168) then
                                    local A;
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    local A;
                                    Stk[Inst[2]] = {};
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = {};
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                end
                            elseif (Enum <= 170) then
                                Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
                            elseif (Enum > 171) then
                                local A;
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                            else
                                local A;
                                Stk[Inst[2]] = {};
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                do
                                    return;
                                end
                            end
                        elseif (Enum <= 176) then
                            if (Enum <= 174) then
                                if (Enum > 173) then
                                    local A;
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                else
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Inst[3]] = Inst[4];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                end
                            elseif (Enum > 175) then
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Stk[A + 1]);
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] ~= Inst[4]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 178) then
                            if (Enum > 177) then
                                local A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                            else
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] ~= Inst[4]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 179) then
                            Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
                        elseif (Enum > 180) then
                            local A;
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = not Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if not Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        else
                            local B = Inst[3];
                            local K = Stk[B];
                            for Idx = B + 1, Inst[4] do
                                K = K .. Stk[Idx];
                            end
                            Stk[Inst[2]] = K;
                        end
                    elseif (Enum <= 199) then
                        if (Enum <= 190) then
                            if (Enum <= 185) then
                                if (Enum <= 183) then
                                    if (Enum == 182) then
                                        Env[Inst[3]] = Stk[Inst[2]];
                                    else
                                        local Edx;
                                        local Results;
                                        local A;
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Stk[A + 1]);
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Env[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
                                        Edx = 0;
                                        for Idx = A, Inst[4] do
                                            Edx = Edx + 1;
                                            Stk[Idx] = Results[Edx];
                                        end
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                    end
                                elseif (Enum == 184) then
                                    Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
                                else
                                    local A;
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Upvalues[Inst[3]] = Stk[Inst[2]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Upvalues[Inst[3]] = Stk[Inst[2]];
                                end
                            elseif (Enum <= 187) then
                                if (Enum > 186) then
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                else
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum <= 188) then
                                local B;
                                local A;
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                B = Stk[Inst[3]];
                                Stk[A + 1] = B;
                                Stk[A] = B[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            elseif (Enum == 189) then
                                local A = Inst[2];
                                local Index = Stk[A];
                                local Step = Stk[A + 2];
                                if (Step > 0) then
                                    if (Index > Stk[A + 1]) then
                                        VIP = Inst[3];
                                    else
                                        Stk[A + 3] = Index;
                                    end
                                elseif (Index < Stk[A + 1]) then
                                    VIP = Inst[3];
                                else
                                    Stk[A + 3] = Index;
                                end
                            else
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                VIP = Inst[3];
                            end
                        elseif (Enum <= 194) then
                            if (Enum <= 192) then
                                if (Enum > 191) then
                                    local Edx;
                                    local Results, Limit;
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    local A;
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum > 193) then
                                local B;
                                local A;
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                B = Stk[Inst[3]];
                                Stk[A + 1] = B;
                                Stk[A] = B[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                B = Stk[Inst[3]];
                                Stk[A + 1] = B;
                                Stk[A] = B[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                B = Stk[Inst[3]];
                                Stk[A + 1] = B;
                                Stk[A] = B[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = #Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Inst[2] < Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                            end
                        elseif (Enum <= 196) then
                            if (Enum > 195) then
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = #Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                            else
                                local Edx;
                                local Results, Limit;
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = #Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = #Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Stk[A + 1]));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A](Unpack(Stk, A + 1, Top));
                            end
                        elseif (Enum <= 197) then
                            local B;
                            local Edx;
                            local Results, Limit;
                            local A;
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Stk[A + 1]));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            B = Stk[Inst[4]];
                            if B then
                                VIP = VIP + 1;
                            else
                                Stk[Inst[2]] = B;
                                VIP = Inst[3];
                            end
                        elseif (Enum == 198) then
                            local B;
                            local A;
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            B = Stk[Inst[4]];
                            if B then
                                VIP = VIP + 1;
                            else
                                Stk[Inst[2]] = B;
                                VIP = Inst[3];
                            end
                        else
                            local A = Inst[2];
                            local Cls = {};
                            for Idx = 1, #Lupvals do
                                local List = Lupvals[Idx];
                                for Idz = 0, #List do
                                    local Upv = List[Idz];
                                    local NStk = Upv[1];
                                    local DIP = Upv[2];
                                    if ((NStk == Stk) and (DIP >= A)) then
                                        Cls[DIP] = NStk[DIP];
                                        Upv[1] = Cls;
                                    end
                                end
                            end
                        end
                    elseif (Enum <= 208) then
                        if (Enum <= 203) then
                            if (Enum <= 201) then
                                if (Enum == 200) then
                                    local Results;
                                    local Edx;
                                    local Results, Limit;
                                    local A;
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                                    Edx = 0;
                                    for Idx = A, Inst[4] do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if not Stk[Inst[2]] then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                end
                            elseif (Enum > 202) then
                                local A = Inst[2];
                                local B = Inst[3];
                                for Idx = A, B do
                                    Stk[Idx] = Vararg[Idx - A];
                                end
                            else
                                local A;
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                            end
                        elseif (Enum <= 205) then
                            if (Enum > 204) then
                                local A;
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                local B;
                                local A;
                                A = Inst[2];
                                B = Stk[Inst[3]];
                                Stk[A + 1] = B;
                                Stk[A] = B[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            end
                        elseif (Enum <= 206) then
                            local A = Inst[2];
                            local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
                            local Edx = 0;
                            for Idx = A, Inst[4] do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                        elseif (Enum > 207) then
                            local Edx;
                            local Results, Limit;
                            local B;
                            local A;
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            B = Stk[Inst[3]];
                            Stk[A + 1] = B;
                            Stk[A] = B[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A](Unpack(Stk, A + 1, Top));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                        else
                            do
                                return;
                            end
                        end
                    elseif (Enum <= 213) then
                        if (Enum <= 210) then
                            if (Enum > 209) then
                                local Edx;
                                local Results, Limit;
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                            else
                                local A;
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 211) then
                            local A = Inst[2];
                            local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                            local Edx = 0;
                            for Idx = A, Inst[4] do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                        elseif (Enum > 212) then
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            VIP = Inst[3];
                        else
                            local Step;
                            local Index;
                            local A;
                            Stk[Inst[2]] = {};
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Index = Stk[A];
                            Step = Stk[A + 2];
                            if (Step > 0) then
                                if (Index > Stk[A + 1]) then
                                    VIP = Inst[3];
                                else
                                    Stk[A + 3] = Index;
                                end
                            elseif (Index < Stk[A + 1]) then
                                VIP = Inst[3];
                            else
                                Stk[A + 3] = Index;
                            end
                        end
                    elseif (Enum <= 215) then
                        if (Enum > 214) then
                            local NewProto = Proto[Inst[3]];
                            local NewUvals;
                            local Indexes = {};
                            NewUvals = Setmetatable({}, {
                                __index = function(_, Key)
                                    local Val = Indexes[Key];
                                    return Val[1][Val[2]];
                                end,
                                __newindex = function(_, Key, Value)
                                    local Val = Indexes[Key];
                                    Val[1][Val[2]] = Value;
                                end
                            });
                            for Idx = 1, Inst[4] do
                                VIP = VIP + 1;
                                local Mvm = Instr[VIP];
                                if (Mvm[1] == 290) then
                                    Indexes[Idx - 1] = {Stk, Mvm[3]};
                                else
                                    Indexes[Idx - 1] = {Upvalues, Mvm[3]};
                                end
                                Lupvals[#Lupvals + 1] = Indexes;
                            end
                            Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
                        else
                            Stk[Inst[2]] = Inst[3] ~= 0;
                            VIP = VIP + 1;
                        end
                    elseif (Enum <= 216) then
                        VIP = Inst[3];
                    elseif (Enum == 217) then
                        local A;
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    else
                        local A = Inst[2];
                        do
                            return Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        end
                    end
                elseif (Enum <= 254) then
                    if (Enum <= 236) then
                        if (Enum <= 227) then
                            if (Enum <= 222) then
                                if (Enum <= 220) then
                                    if (Enum == 219) then
                                        local A;
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    else
                                        local Edx;
                                        local Results, Limit;
                                        local B;
                                        local A;
                                        A = Inst[2];
                                        B = Stk[Inst[3]];
                                        Stk[A + 1] = B;
                                        Stk[A] = B[Inst[4]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Stk[Inst[3]];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                        Top = (Limit + A) - 1;
                                        Edx = 0;
                                        for Idx = A, Top do
                                            Edx = Edx + 1;
                                            Stk[Idx] = Results[Edx];
                                        end
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        A = Inst[2];
                                        Stk[A](Unpack(Stk, A + 1, Top));
                                        VIP = VIP + 1;
                                        Inst = Instr[VIP];
                                        Stk[Inst[2]] = Inst[3];
                                    end
                                elseif (Enum > 221) then
                                    if (Inst[2] < Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    local A;
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Upvalues[Inst[3]] = Stk[Inst[2]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Upvalues[Inst[3]] = Stk[Inst[2]];
                                end
                            elseif (Enum <= 224) then
                                if (Enum == 223) then
                                    local A;
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    VIP = Inst[3];
                                end
                            elseif (Enum <= 225) then
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = {};
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                VIP = Inst[3];
                            elseif (Enum == 226) then
                                local A;
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                            end
                        elseif (Enum <= 231) then
                            if (Enum <= 229) then
                                if (Enum == 228) then
                                    local Results;
                                    local Edx;
                                    local Results, Limit;
                                    local A;
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                                    Edx = 0;
                                    for Idx = A, Inst[4] do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    local A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                end
                            elseif (Enum == 230) then
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            else
                                local B;
                                local A;
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                B = Stk[Inst[4]];
                                if B then
                                    VIP = VIP + 1;
                                else
                                    Stk[Inst[2]] = B;
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 233) then
                            if (Enum > 232) then
                                local Edx;
                                local Results, Limit;
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                            else
                                local A;
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 234) then
                            local B = Stk[Inst[4]];
                            if not B then
                                VIP = VIP + 1;
                            else
                                Stk[Inst[2]] = B;
                                VIP = Inst[3];
                            end
                        elseif (Enum > 235) then
                            local Results;
                            local Edx;
                            local Results, Limit;
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                            Edx = 0;
                            for Idx = A, Inst[4] do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = {};
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = {};
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = {};
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            VIP = Inst[3];
                        else
                            local Results;
                            local Edx;
                            local Results, Limit;
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                            Edx = 0;
                            for Idx = A, Inst[4] do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        end
                    elseif (Enum <= 245) then
                        if (Enum <= 240) then
                            if (Enum <= 238) then
                                if (Enum > 237) then
                                    local Edx;
                                    local Results;
                                    local A;
                                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results = {Stk[A](Stk[A + 1])};
                                    Edx = 0;
                                    for Idx = A, Inst[4] do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Env[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Stk[A + 1]);
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Upvalues[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    if (Stk[Inst[2]] == Stk[Inst[4]]) then
                                        VIP = VIP + 1;
                                    else
                                        VIP = Inst[3];
                                    end
                                else
                                    local A = Inst[2];
                                    Stk[A](Unpack(Stk, A + 1, Top));
                                end
                            elseif (Enum > 239) then
                                local A;
                                Stk[Inst[2]] = {};
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                for Idx = Inst[2], Inst[3] do
                                    Stk[Idx] = nil;
                                end
                            end
                        elseif (Enum <= 242) then
                            if (Enum > 241) then
                                local A = Inst[2];
                                local B = Stk[Inst[3]];
                                Stk[A + 1] = B;
                                Stk[A] = B[Inst[4]];
                            else
                                local A;
                                A = Inst[2];
                                Stk[A] = Stk[A]();
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                do
                                    return Stk[Inst[2]];
                                end
                            end
                        elseif (Enum <= 243) then
                            local A;
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                        elseif (Enum == 244) then
                            local A = Inst[2];
                            Stk[A] = Stk[A](Stk[A + 1]);
                        else
                            local B = Stk[Inst[4]];
                            if B then
                                VIP = VIP + 1;
                            else
                                Stk[Inst[2]] = B;
                                VIP = Inst[3];
                            end
                        end
                    elseif (Enum <= 249) then
                        if (Enum <= 247) then
                            if (Enum > 246) then
                                local Edx;
                                local Results;
                                local A;
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results = {Stk[A](Stk[A + 1])};
                                Edx = 0;
                                for Idx = A, Inst[4] do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = {};
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                            elseif not Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        elseif (Enum == 248) then
                            local Edx;
                            local Results;
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results = {Stk[A](Stk[A + 1])};
                            Edx = 0;
                            for Idx = A, Inst[4] do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        else
                            local A;
                            A = Inst[2];
                            Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3] ~= 0;
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            VIP = Inst[3];
                        end
                    elseif (Enum <= 251) then
                        if (Enum == 250) then
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                        else
                            local A;
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                        end
                    elseif (Enum <= 252) then
                        Stk[Inst[2]] = Inst[3] ~= 0;
                    elseif (Enum > 253) then
                        local Edx;
                        local Results, Limit;
                        local A;
                        Stk[Inst[2]] = Env[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                        Top = (Limit + A) - 1;
                        Edx = 0;
                        for Idx = A, Top do
                            Edx = Edx + 1;
                            Stk[Idx] = Results[Edx];
                        end
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        if (Stk[Inst[2]] == Stk[Inst[4]]) then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    else
                        local A;
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    end
                elseif (Enum <= 272) then
                    if (Enum <= 263) then
                        if (Enum <= 258) then
                            if (Enum <= 256) then
                                if (Enum > 255) then
                                    local Edx;
                                    local Results, Limit;
                                    local B;
                                    local A;
                                    A = Inst[2];
                                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    B = Stk[Inst[3]];
                                    Stk[A + 1] = B;
                                    Stk[A] = B[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                    Top = (Limit + A) - 1;
                                    Edx = 0;
                                    for Idx = A, Top do
                                        Edx = Edx + 1;
                                        Stk[Idx] = Results[Edx];
                                    end
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    Stk[A](Unpack(Stk, A + 1, Top));
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    A = Inst[2];
                                    B = Stk[Inst[3]];
                                    Stk[A + 1] = B;
                                    Stk[A] = B[Inst[4]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Stk[Inst[3]];
                                    VIP = VIP + 1;
                                    Inst = Instr[VIP];
                                    Stk[Inst[2]] = Inst[3];
                                else
                                    Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
                                end
                            elseif (Enum == 257) then
                                local A;
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                VIP = Inst[3];
                            else
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if not Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum <= 260) then
                            if (Enum == 259) then
                                Stk[Inst[2]] = {};
                            else
                                local Results;
                                local Edx;
                                local Results, Limit;
                                local A;
                                Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                                Top = (Limit + A) - 1;
                                Edx = 0;
                                for Idx = A, Top do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                                Edx = 0;
                                for Idx = A, Inst[4] do
                                    Edx = Edx + 1;
                                    Stk[Idx] = Results[Edx];
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = {};
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = {};
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                VIP = Inst[3];
                            end
                        elseif (Enum <= 261) then
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                        elseif (Enum > 262) then
                            local A;
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                        else
                            local Edx;
                            local Results, Limit;
                            local B;
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            B = Stk[Inst[3]];
                            Stk[A + 1] = B;
                            Stk[A] = B[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A](Unpack(Stk, A + 1, Top));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            B = Stk[Inst[3]];
                            Stk[A + 1] = B;
                            Stk[A] = B[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                            Top = (Limit + A) - 1;
                            Edx = 0;
                            for Idx = A, Top do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A](Unpack(Stk, A + 1, Top));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                        end
                    elseif (Enum <= 267) then
                        if (Enum <= 265) then
                            if (Enum == 264) then
                                local A;
                                Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            else
                                local A;
                                A = Inst[2];
                                Stk[A] = Stk[A]();
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if (Stk[Inst[2]] <= Stk[Inst[4]]) then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum == 266) then
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            VIP = Inst[3];
                        else
                            local Edx;
                            local Results;
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            for Idx = Inst[2], Inst[3] do
                                Stk[Idx] = nil;
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
                            Edx = 0;
                            for Idx = A, Inst[4] do
                                Edx = Edx + 1;
                                Stk[Idx] = Results[Edx];
                            end
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if not Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        end
                    elseif (Enum <= 269) then
                        if (Enum > 268) then
                            Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                        else
                            local A;
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Stk[A + 1]);
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            VIP = Inst[3];
                        end
                    elseif (Enum <= 270) then
                        local Edx;
                        local Results, Limit;
                        local A;
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                        Top = (Limit + A) - 1;
                        Edx = 0;
                        for Idx = A, Top do
                            Edx = Edx + 1;
                            Stk[Idx] = Results[Edx];
                        end
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                    elseif (Enum > 271) then
                        local B;
                        local Edx;
                        local Results, Limit;
                        local A;
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                        Top = (Limit + A) - 1;
                        Edx = 0;
                        for Idx = A, Top do
                            Edx = Edx + 1;
                            Stk[Idx] = Results[Edx];
                        end
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        B = Stk[Inst[4]];
                        if not B then
                            VIP = VIP + 1;
                        else
                            Stk[Inst[2]] = B;
                            VIP = Inst[3];
                        end
                    else
                        local A;
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = {};
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        VIP = Inst[3];
                    end
                elseif (Enum <= 281) then
                    if (Enum <= 276) then
                        if (Enum <= 274) then
                            if (Enum == 273) then
                                local A;
                                Stk[Inst[2]] = Upvalues[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            else
                                local VA;
                                local A;
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Inst[3];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Top = (A + Varargsz) - 1;
                                for Idx = A, Top do
                                    VA = Vararg[Idx - A];
                                    Stk[Idx] = VA;
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Top = (A + Varargsz) - 1;
                                for Idx = A, Top do
                                    VA = Vararg[Idx - A];
                                    Stk[Idx] = VA;
                                end
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                A = Inst[2];
                                Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Stk[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                Stk[Inst[2]] = Env[Inst[3]];
                                VIP = VIP + 1;
                                Inst = Instr[VIP];
                                if Stk[Inst[2]] then
                                    VIP = VIP + 1;
                                else
                                    VIP = Inst[3];
                                end
                            end
                        elseif (Enum == 275) then
                            Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
                        else
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3] ~= 0;
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3] ~= 0;
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3] ~= 0;
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3] ~= 0;
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3] ~= 0;
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3] ~= 0;
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        end
                    elseif (Enum <= 278) then
                        if (Enum == 277) then
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Env[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if not Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        else
                            local K;
                            local B;
                            local A;
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Inst[3];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            B = Inst[3];
                            K = Stk[B];
                            for Idx = B + 1, Inst[4] do
                                K = K .. Stk[Idx];
                            end
                            Stk[Inst[2]] = K;
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            B = Stk[Inst[4]];
                            if not B then
                                VIP = VIP + 1;
                            else
                                Stk[Inst[2]] = B;
                                VIP = Inst[3];
                            end
                        end
                    elseif (Enum <= 279) then
                        Upvalues[Inst[3]] = Stk[Inst[2]];
                    elseif (Enum > 280) then
                        local Edx;
                        local Results, Limit;
                        local A;
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                        Top = (Limit + A) - 1;
                        Edx = 0;
                        for Idx = A, Top do
                            Edx = Edx + 1;
                            Stk[Idx] = Results[Edx];
                        end
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        if Stk[Inst[2]] then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    else
                        do
                            return Stk[Inst[2]];
                        end
                    end
                elseif (Enum <= 286) then
                    if (Enum <= 283) then
                        if (Enum == 282) then
                            local A = Inst[2];
                            Stk[A] = Stk[A]();
                        else
                            local A;
                            Stk[Inst[2]] = Stk[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            A = Inst[2];
                            Stk[A] = Stk[A](Stk[A + 1]);
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            Stk[Inst[2]] = Upvalues[Inst[3]];
                            VIP = VIP + 1;
                            Inst = Instr[VIP];
                            if Stk[Inst[2]] then
                                VIP = VIP + 1;
                            else
                                VIP = Inst[3];
                            end
                        end
                    elseif (Enum <= 284) then
                        local Results;
                        local Edx;
                        local Results, Limit;
                        local A;
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                        Top = (Limit + A) - 1;
                        Edx = 0;
                        for Idx = A, Top do
                            Edx = Edx + 1;
                            Stk[Idx] = Results[Edx];
                        end
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Results = {Stk[A](Unpack(Stk, A + 1, Top))};
                        Edx = 0;
                        for Idx = A, Inst[4] do
                            Edx = Edx + 1;
                            Stk[Idx] = Results[Edx];
                        end
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Env[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A]();
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        for Idx = Inst[2], Inst[3] do
                            Stk[Idx] = nil;
                        end
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        if Stk[Inst[2]] then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    elseif (Enum > 285) then
                        local A;
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]][Inst[3]] = Inst[4];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Env[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A]();
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        if not Stk[Inst[2]] then
                            VIP = VIP + 1;
                        else
                            VIP = Inst[3];
                        end
                    else
                        local Edx;
                        local Results, Limit;
                        local B;
                        local A;
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        B = Stk[Inst[3]];
                        Stk[A + 1] = B;
                        Stk[A] = B[Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                        Top = (Limit + A) - 1;
                        Edx = 0;
                        for Idx = A, Top do
                            Edx = Edx + 1;
                            Stk[Idx] = Results[Edx];
                        end
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A](Unpack(Stk, A + 1, Top));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Env[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                    end
                elseif (Enum <= 288) then
                    if (Enum == 287) then
                        local T;
                        local Edx;
                        local Results, Limit;
                        local A;
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = {};
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Inst[3];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
                        Top = (Limit + A) - 1;
                        Edx = 0;
                        for Idx = A, Top do
                            Edx = Edx + 1;
                            Stk[Idx] = Results[Edx];
                        end
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        A = Inst[2];
                        T = Stk[A];
                        for Idx = A + 1, Top do
                            Insert(T, Stk[Idx]);
                        end
                    else
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]][Inst[3]] = Inst[4];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Upvalues[Inst[3]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        Stk[Inst[2]][Inst[3]] = Inst[4];
                        VIP = VIP + 1;
                        Inst = Instr[VIP];
                        VIP = Inst[3];
                    end
                elseif (Enum <= 289) then
                    local A;
                    Stk[Inst[2]] = Upvalues[Inst[3]];
                    VIP = VIP + 1;
                    Inst = Instr[VIP];
                    Stk[Inst[2]] = Inst[3];
                    VIP = VIP + 1;
                    Inst = Instr[VIP];
                    Stk[Inst[2]] = Inst[3];
                    VIP = VIP + 1;
                    Inst = Instr[VIP];
                    A = Inst[2];
                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
                    VIP = VIP + 1;
                    Inst = Instr[VIP];
                    if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
                        VIP = VIP + 1;
                    else
                        VIP = Inst[3];
                    end
                elseif (Enum > 290) then
                    local B;
                    local Edx;
                    local Results, Limit;
                    local A;
                    Stk[Inst[2]] = Inst[3];
                    VIP = VIP + 1;
                    Inst = Instr[VIP];
                    Stk[Inst[2]] = Env[Inst[3]];
                    VIP = VIP + 1;
                    Inst = Instr[VIP];
                    Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
                    VIP = VIP + 1;
                    Inst = Instr[VIP];
                    Stk[Inst[2]] = Stk[Inst[3]];
                    VIP = VIP + 1;
                    Inst = Instr[VIP];
                    A = Inst[2];
                    Results, Limit = _R(Stk[A](Stk[A + 1]));
                    Top = (Limit + A) - 1;
                    Edx = 0;
                    for Idx = A, Top do
                        Edx = Edx + 1;
                        Stk[Idx] = Results[Edx];
                    end
                    VIP = VIP + 1;
                    Inst = Instr[VIP];
                    A = Inst[2];
                    Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
                    VIP = VIP + 1;
                    Inst = Instr[VIP];
                    Stk[Inst[2]] = Stk[Inst[3]];
                    VIP = VIP + 1;
                    Inst = Instr[VIP];
                    B = Stk[Inst[4]];
                    if B then
                        VIP = VIP + 1;
                    else
                        Stk[Inst[2]] = B;
                        VIP = Inst[3];
                    end
                else
                    Stk[Inst[2]] = Stk[Inst[3]];
                end
                VIP = VIP + 1;
            end
        end;
    end
    return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall(
    "LOL!AB012Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403183Q004C6567656E6461727953652Q74696E6773436C612Q736963030B3Q00426967576967734461746103083Q00514CC85C0476795A03063Q00111C29BB2F65028Q0003063Q0001092FB0052103053Q006152665ADE03063Q0048724461746103083Q000DAA58D363A936BF03063Q00CC4ECB2BA737034Q00030C3Q0072BCA92F1B8F41A0A62F379803063Q00DC31C5CA437E03073Q00E4DD5D3B5E29E803063Q0064A7A43E573B010003093Q00A34F43C5E23727894203073Q0049E03620A9876203053Q00FCC47C215A03073Q00ADA8AB1744349D00030A3Q00A9FB65DCD1B5F57FF2DA03053Q00BFE794119503073Q001EF8FA8CABEEDF03083Q00454D889FE0C7A79B030D3Q00E6F6E175D7E3DA7CFFF2FF77D703043Q0012B29793030D3Q004E8DEF4BC16EA5F37EC5748BF803053Q00A41AEC9D2C030E3Q00784E492D175866551902404E482203053Q00722C2F3B4A030A3Q00476C6F62616C4461746103073Q0037A320DDD92D9703053Q00B564D345B103053Q002AD2B4560C03043Q003A69ABD7030E3Q00D6E68E4EE576E2E7B54DE67EF9EC03063Q00199589E12281030C3Q00DCE637F4C0BB37F7EE39F2C703073Q00529A8F509CB4E9030E3Q0016054D433400D29B3D264D42380003083Q00D2536B282E5D65A1030E3Q00F38E2B3FDF853D1BD8B22F3CD18503043Q0052B6E04E030D3Q006BFFD5E5873956CADAF085084D03063Q006D399EBB82E2030E3Q000C30EDF02A36F6FF163AF5E13B2D03043Q00915E5F99030B3Q004372656174654672616D6503053Q00DBDF15D84B03063Q00D79DAD74B52E030D3Q0052656769737465724576656E7403143Q000598AACBFF078BB9D7FD109AB4D7F41496A7D7FE03053Q00BA55D4EB9203153Q00F2AD37C71CDC67F0A431DB17D17CEBB237DC15CB7C03073Q0038A2E1769E598E03093Q0053657453637269707403073Q00730BE5B927D64803063Q00B83C65A0CF4203023Q005F47030D3Q004C44697370656C43616368654C024Q00509413412Q01024Q0058941341024Q0048C21341024Q00C8CE1541024Q0024411841024Q00806A1441024Q005C091541024Q004068DD40024Q004C0D1441024Q00580F1441024Q0098690B41024Q00302F1441024Q00289A1541024Q00346E1541024Q0034651541024Q0050DA0241024Q004C321541024Q00B4641641024Q00804A1641024Q00B84B1641024Q00E0AA1341024Q0028B10D41024Q00D8590D41024Q0060C20B41024Q0038F90B41024Q0040D91641024Q00980A1741024Q003CD01841024Q00ECC01741024Q00E0F71041024Q0014EA1941024Q00B4AA1841025Q00C31841024Q0098BF1841024Q0064601941024Q00085D1941024Q008C381941024Q000C3A1941024Q0004F31941024Q003C801941024Q0054C61A41024Q00343E1B41024Q00BC2A1C41024Q00D02A1C41024Q00F42A1C41025Q002B1C41024Q000C2B1C41024Q00F8311C41024Q00D4361A41024Q0068E91C41024Q00C4E91C4103043Q0028307CE203073Q00EB667F32A7CC12030B3Q0072AEE02F402B42A7FC305003063Q004E30C195432403103Q001110891540241B845865251B8C11522403053Q0021507EE078031B3Q0044756E67656F6E2Q6572277320547261696E696E672044752Q6D7903173Q00526169646572277320547261696E696E672044752Q6D79030E3Q00D8BA02CD52E5A6048478F9A50EDD03053Q003C8CC863A4031E3Q00426C61636B20447261676F6E2773204368612Q6C656E67652044752Q6D7903153Q00A4F80127B482B43034A38EFA0D28A5C7D0112BAF9E03053Q00C2E794644603113Q006843D3AEF7C40678C0ADFD886259CCAEEF03063Q00A8262CA1C39603123Q00B0EAB23604FAB71F8EF58C7170CCA31B8DE503083Q0076E09CE2165088D603183Q0077E05D8550ED50945BAE699243ED4D8941EB19A457E3549903043Q00E0228E3903163Q0052616964657227732054616E6B696E672044752Q6D79031A3Q0044756E67656F6E2Q657227732054616E6B696E672044752Q6D7903143Q00EDB0C4CF7EB1691CDFAECBD47DF61D2ACBAAC8C403083Q006EBEC7A5BD13913D03143Q00F4E465E58ACB9AC372E987CED4EC37CC9ECAD7F203063Q00A7BA8B1788EB03123Q003EA0860A1FBA864D2EB486065A919D0017AC03043Q006D7AD5E803153Q00C5FEAE3CEFF5AE35AED3A33DEFF0A770CAE2AF3DF703043Q00508E97C2030C3Q0037C7654B06D2376816CB7A5503043Q002C63A61703193Q00496E697469617465277320547261696E696E672044752Q6D7903143Q0058E2273136AB72B70D373EA57BF2691226A971EE03063Q00C41C9749565303163Q00426F786572277320547261696E696E672044752Q6D7903173Q00C3112C0084571762B3373B118B561178F4430D058F550103083Q001693634970E2387803183Q005665746572616E277320547261696E696E672044752Q6D7903193Q004469736369706C65277320547261696E696E672044752Q6D79031C3Q0045626F6E204B6E69676874277320547261696E696E672044752Q6D7903163Q008C7D2QE78CB57A2QF0CD9B7AEFF78CAC35C6E080B56C03053Q00EDD815829503213Q00AF414D4BB1DB1EB64B5E52F0E85A944F515CB5CD1EB64F4D58B5DD1EA65B2Q52A903073Q003EE22E2Q3FD0A903123Q00C2175A8F134D1B5FF71E50975F293A53E80003083Q003E857935E37F6D4F031A3Q00251661E79B87AF00063DE3D3AAE2241520F2D3BAE234013FF8CF03073Q00C270745295B6CE030C3Q001AA7411AC1F64E1DBD4115D903073Q006E59C82C78A08203153Q008AC75D474D493E49EBF74A54444F2F0D8FD6464B5A03083Q002DCBA32B26232A5B03103Q00F38BDD3788A45DD184D063A3BC59DF9C03073Q0034B2E5BC43E7C903193Q00054E4503B7682632551049B77426204D590AF01C07344C5D1D03073Q004341213064973C03153Q00FCE8A3DAF2CBA79ADDE0CBA78ACDFED2FEEE89A28D03053Q0093BF87CEB803143Q00A727ABC3D947F2B02DB5D59877A78925BF81800B03073Q00D2E448C6A1B83303143Q001546FE1272DA767DF603678E125CFE1D6A8E6F1B03063Q00AE562993701303143Q00780F8009241B519F5E13994B011A1CA64240D45803083Q00CB3B60ED6B456F7103183Q00101EA9F330FDD83613ECC23EFDD52502ECC524FDDA3D56F803073Q00B74476CC81519003153Q002DA27DE60A964E9975F71FC22AB87DE912C25FFD2203063Q00E26ECD10846B03153Q00C8CCEDDB40FF83D4DC52FF83C4CC4CE6DAA08810B803053Q00218BA380B9030F3Q0047697A6C6F636B27732044752Q6D7903193Q007E5514DF544C44EA524B109E734D09D34E18499E705105D04303043Q00BE37386403133Q007BB628161AE0B372AE311F14E6B372BA31130A03073Q009336CF5C7E738303133Q00233E27700C724D1534700C790871116800731403063Q001E6D51551D6D031E3Q00DC7E59B437CABCCB7447A276FAE9F27C4DF6678EACBF3978B331D7F3F13803073Q009C9F1134D656BE03153Q008DE0B0BEAFFBFD88ABFCA9FC8AFAB0B1B7AF2QECFD03043Q00DCCE8FDD03153Q00A5722015D9D892B2783E0398E8C78B703457899D8203073Q00B2E61D4D77B8AC031E3Q00D6B1071976ECB58A0F0863B8D1AB07166EB8A4EC5A5B59F7B59F181678EA03063Q009895DE6A7B17031D3Q00FE29FB41B4C966C246A6C966D256B8D03FB615E59D08F90394CF2BF95103053Q00D5BD469623031E3Q006C5A790A4E41343C4A4660486B407905561522580F677B075B1547184E5803043Q00682F3514032C3Q0080438C1EBD1BE378840FA84F87598C11A54FF51CC12FAC0AAF40C13FBD1BA044C11DB20BE37E8410B90EB04903063Q006FC32CE17CDC03143Q00FB490D71AABF98720560BFEBFC530D7EB2EB801303063Q00CBB8266013CB03143Q001A7C7443CF2D334D44DD2D335D54C3346A39199903053Q00AE5913192103143Q000C1D5F4CF6934B1B17415AB7A31E221F4B0EAED703073Q006B4F72322E97E703133Q001EB4BA3C9A799FC538AABC278D7993D534ABAC03083Q00A059C6D549EA59D7031E3Q006078B3F6856041F4D6C0497DBDF0C20845B1EDD10855A1F3C85131E5AF9603053Q00A52811D49E03263Q00CDD00F3B66CDE948182FE9D509312AE0992B3C2BE7D81C7312E0CA1C7302F0D4052A66B4885B03053Q004685B9685303193Q002D48542BCA1005702FDA1005603FC4095C04678926494529C203053Q00A96425244A03183Q00298AB2510393E2640594B6102492AF5D19C7EF10228BB75503043Q003060E7C203193Q00E1571E2C1ACCEFB7CD491A6D3DCDA28ED11A436D3ECAAA86C603083Q00E3A83A6E4D79B8CF03183Q005231AF41B2CF31917E2FAB0095CE7CA8627CF2009AD475AA03083Q00C51B5CDF20D1BB1103183Q002A52D3FA004B83CF064CD7BB274ACEF61A1F8EBB2C58D1FE03043Q009B633FA303173Q00ABDCB18CBA90C2E5A49EADC4A6C4AC80A0C4CF919388BD03063Q00E4E2B1C1EDD9031A3Q001DBD33E737A463D231A337A610A52EEB2DF06EA607B822E23BA703043Q008654D043031A3Q003AA1965D10B8C66816BF921C37B98B510AECCB1C25BE9F5706A003043Q003C73CCE603263Q00CB3BF962FE7ADF75F42EAB53E837E971F37ACF65EA37F230AA7ACD71E42EE27FE97ABA21BE6E03043Q0010875A8B03233Q007875142157144C516712736D5B75567512736A4175596D467E0E727957600F3C40142F03073Q0018341466532E3403123Q00E9262F2B1D840B20290EC32A61001AC9223803053Q006FA44F414403163Q00E8D89BC63CEBCBD8909E0DE5CBDB82CA6ECED3D48EC703063Q008AA6B9E3BE4E030E3Q00FB66C434462A1ACE34E1225F2E0003073Q0079AB14A557324303113Q00F439B032F926C735B831BC42E22DB43BA003063Q0062A658D956D9030F3Q00C4F77005C6E8F7F87241A2C92QFB6003063Q00BC2Q961961E603133Q00E8884F1603FF9ABD5E100BE8CEC97B1701E0C303063Q008DBAE93F626C030D3Q00C5EF3FA22CFFED6C9230FCE73503053Q0045918A4CD603173Q0044CA9A9DB618778FBD8CBC1E30FB9B8CBA5654DA2Q84A603063Q007610AF2QE9DF03123Q00BF8D38BEEACB598A8934BCEBCB599E8938A203073Q001DEBE455DB8EEB03163Q0008DABBCF7A41355739949EDC7A4F20577DF0AFD07A5703083Q00325DB4DABD172E4703173Q00E8AD485945D008EAA1485804F85DD3A9420C68DD5AD9A103073Q0028BEC43B2C24BC03183Q000A4CCFA1FB714D0840CFA0BA59183148C5F4D778093550D103073Q006D5C25BCD49A1D03173Q0032E6B7D6305644DBA1D0251A20FAA9CE281A37E2A5CF3D03063Q003A648FC4A35103143Q0057617275672773205461726765742044752Q6D7903113Q002D4722A87F6DE4031B4526E31B5CE83Q03083Q006E7A2243C35F2985030F3Q0042B45A419641B055419651A45647CF03053Q00B615D13B2A031B3Q008C73EB291CFE9458C81F20AAF763C00E35FE9342C81038FEE6079503063Q00DED737A57D4103173Q0008E1F55AC1D4FF5C252QC718FBCDE45E3591E20FFFCCF403083Q002A4CB1A67A92A18D030A3Q0086981CDD6D77A98704D903063Q0016C5EA65AE1903083Q000631A9CC70A6C49203083Q00E64D54C5BC16CFB703043Q00D73BE8D903083Q00559974A69CECC19003043Q008ACF639603063Q0060C4802DD38403043Q001BA2557A03083Q00B855ED1B3FB2CFD403043Q002676277A03043Q003F68396903143Q006E616D65706C6174654C556E697473436163686503193Q006E616D65706C6174654C556E69747343616368654672616D6503053Q00F1EA6612F203043Q005FB7B827030B3Q00696E697469616C697A6564026Q00F03F03173Q009B1ECA036BB02E940BC21961AE2B8100D50379AF34901B03073Q0062D55F874634E003173Q00D28CE8537DD084F64477CC86EC596BDA8AFA5676D286ED03053Q00349EC3A917027Q004003073Q0055B21762833B6F03083Q00EB1ADC5214E6551B03153Q00F317CC2BDD04FC1EC326DD04EA15CA2DCF19F117C903063Q0056A35B8D729803153Q007D2A595605632755471F6C3E2Q5A0E6C2A50571F7703053Q005A336B1413031F3Q0048616E646C654C4E616D65706C617465556E6974734361636865412Q64656403213Q0048616E646C654C4E616D65706C617465556E697473436163686552656D6F766564030C3Q004C52616E6765436865636B4C030A3Q00719ECB4EF5036B0029DE03083Q003118EAAE23CF325D026Q001040030A3Q0005E6F8852B5FA5AADA2603053Q00116C929DE8026Q001440030A3Q0042D711E075F91E9B46BB03063Q00C82BA3748D4F030A3Q00B622388EEAA2B0EB646A03073Q0083DF565DE3D094030A3Q00EA51B3BB47E6B716E0EE03063Q00D583252QD67D026Q001C40030A3Q002F3F20B2BB757976EDB003053Q0081464B45DF030A3Q004FDFF6E426BE119DA1BF03063Q008F26AB93891C030A3Q00D996BCFE59B08780D4E003073Q00B4B0E2D9936383026Q002E40030A3Q00DAAD2A0A89E87F5187EC03043Q0067B3D94F026Q003440030A3Q0043A319D81BDEF718E14403073Q00C32AD77CB521EC026Q00394003083Q00044D32337FA05E0C03063Q00986D39575E45026Q003E4003093Q00F0C30FAEE48B07FAA103083Q00C899B76AC3DEB234030A3Q003BF78D30130866B1DE6403063Q003A5283E85D29025Q0080414003093Q008A43D518076ED00E8903063Q005FE337B0753D030A3Q00116A2646F14A26741DFC03053Q00CB781E432B026Q00444003093Q00F83148E283A57C19BA03053Q00B991452D8F030A3Q00830B1CAB86D94D4FFF8403053Q00BCEA7F79C6025Q00804640030B3Q003126168E626342D569614A03043Q00E3585273026Q004940030A3Q004A0BBFAA58201147E8F203063Q0013237FDAC762026Q004E40030A3Q0015EF0FEF46AF5BB04AAE03043Q00827C9B6A025Q00805140030A3Q00DCDFF3A2F9A529ED829303083Q00DFB5AB96CFC3961C026Q005440030A3Q00452EE6A3531F69B2FF5003053Q00692C5A83CE026Q00594003053Q00706169727303093Q00756E6974506C61746503083Q00756E69744E616D6503083Q00746F6E756D62657203063Q00756E6974496403043Q0066696E6403053Q00DB2604072B03063Q00989F53696A52026Q00204003133Q00556E6974412Q66656374696E67436F6D626174030C3Q00556E69745265616374696F6E03063Q0091CA50EBCC4E03063Q003CE1A63192A903063Q003F122E33041503063Q00674F7E4F4A61030B3Q00556E6974496E5061727479030C3Q00AE7EC1745B0EAE7EC1745B0E03063Q007ADA1FB3133E030A3Q00556E6974496E52616964030C3Q00A7D7DFC6CCB551B2C4CAC4DD03073Q0025D3B6ADA1A9C1030A3Q00556E69744973556E6974030C3Q00E33B5FDE2D6FADF6284ADC3C03073Q00D9975A2DB9481B03063Q00D370E60B53D103053Q0036A31C877203063Q0038D75C9B4B6D03063Q001F48BB3DE22E03063Q00D70751D5426A03073Q0044A36623B2271E03063Q00AE7CDBDE06A703083Q0071DE10BAA763D5E303063Q003A0FE9F12B1A03043Q00964E6E9B03063Q0091C435E6A10A03083Q0020E5A54781C47EDF030C3Q00556E697473496E4D656C2Q65030C3Q00556E697473496E52616E676503063Q0054617267657403143Q00496E74652Q727570744C4672616D65436163686503053Q00E5BBE5ACA403063Q00B5A3E9A42QE103143Q00496E74652Q727570744C556E6974734361636865030C3Q004B69636B5370652Q6C49647303053Q009CF01BEBE003053Q0085DA827A8603163Q0011E6CFC1DBA63638FEF1DDE9B33C3DEBE6E2CEA2353903073Q00585C9F83A4BCC303083Q005549506172656E7403083Q0053652Q74696E677303093Q00833EAA78DBE2D9853C03073Q00BDE04EDF2BB78B026Q33D33F03083Q0001F2BF06C52FE88F03053Q00A14E9CEA7600BF042Q001215012Q00013Q00206Q000200122Q000100013Q00202Q00010001000300122Q000200013Q00202Q00020002000400122Q000300053Q00062Q0003000A000100010004D83Q000A0001001255000300063Q0020E6000400030007001255000500083Q0020E6000500050009001255000600083Q0020E600060006000A0006D700073Q000100062Q0022012Q00064Q0022017Q0022012Q00044Q0022012Q00014Q0022012Q00024Q0022012Q00054Q00070008000A3Q00122Q000A000B6Q000B3Q00024Q000C00073Q00122Q000D000D3Q00122Q000E000E6Q000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D00103Q00122Q000E00116Q000C000E000200202Q000B000C000F00102Q000A000C000B4Q000B3Q000A4Q000C00073Q00122Q000D00133Q00122Q000E00146Q000C000E000200202Q000B000C00154Q000C00073Q00122Q000D00163Q00122Q000E00176Q000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D00183Q00122Q000E00196Q000C000E000200202Q000B000C001A4Q000C00073Q00122Q000D001B3Q00122Q000E001C6Q000C000E000200202Q000B000C001A4Q000C00073Q00122Q000D001D3Q00122Q000E001E6Q000C000E000200202Q000B000C001F4Q000C00073Q00122Q000D00203Q00122Q000E00216Q000C000E000200202Q000B000C001A4Q000C00073Q00122Q000D00223Q00122Q000E00236Q000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D00243Q00122Q000E00256Q000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D00263Q00122Q000E00276Q000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D00283Q00122Q000E00296Q000C000E000200202Q000B000C000F00102Q000A0012000B4Q000B3Q00084Q000C00073Q00122Q000D002B3Q00122Q000E002C6Q000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D002D3Q00122Q000E002E6Q000C000E000200202Q000B000C001A4Q000C00073Q00122Q000D002F3Q00122Q000E00304Q0060000C000E000200202Q000B000C001A4Q000C00073Q00122Q000D00313Q00122Q000E00326Q000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D00333Q00122Q000E00344Q0060000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D00353Q00122Q000E00366Q000C000E000200202Q000B000C000F4Q000C00073Q00122Q000D00373Q00122Q000E00384Q00E5000C000E00020020A0000B000C000F2Q00FA000C00073Q00122Q000D00393Q00122Q000E003A6Q000C000E000200202Q000B000C001500102Q000A002A000B00122Q000B003B6Q000C00073Q00122Q000D003C3Q00122Q000E003D4Q0011000C000E5Q00010B3Q000200202Q000C000B003E4Q000E00073Q00122Q000F003F3Q00122Q001000406Q000E00106Q000C3Q000100202Q000C000B003E4Q000E00073Q00122Q000F00413Q001206001000424Q0056000E00106Q000C3Q000100202Q000C000B00434Q000E00073Q00122Q000F00443Q00122Q001000456Q000E001000020006D7000F0001000100022Q0022012Q00074Q0022012Q000A4Q0001000C000F00010006D7000C0002000100022Q0022012Q000A4Q0022012Q00073Q0006D7000D0003000100022Q0022012Q000A4Q0022012Q00073Q0006D7000E0004000100022Q0022012Q00074Q0022012Q000A3Q0006D7000F0005000100022Q0022012Q00074Q0022012Q000A3Q0006D700100006000100012Q0022012Q00073Q001255001100463Q001255001200463Q0020E60012001200470006F6001200B1000100010004D83Q00B100012Q000301125Q0010260011004700122Q00A900113Q001D00302Q00110048004900302Q0011004A004900302Q0011004B004900302Q0011004C004900302Q0011004D004900302Q0011004E004900302Q0011004F004900302Q00110050004900302Q00110051004900302Q00110052004900302Q00110053004900302Q00110054004900302Q00110055004900302Q00110056004900302Q00110057004900302Q00110058004900302Q00110059004900302Q0011005A004900302Q0011005B004900302Q0011005C004900302Q0011005D004900302Q0011005E004900302Q0011005F004900302Q00110060004900302Q00110061004900302Q00110062004900302Q00110063004900302Q00110064004900302Q00110065004900302Q00110066004900302Q00110067004900302Q00110068004900302Q00110069004900302Q0011006A004900302Q0011006B004900302Q0011006C004900302Q0011006D004900302Q0011006E004900302Q0011006F004900302Q00110070004900302Q00110071004900302Q00110072004900302Q00110073004900302Q00110074004900302Q00110075004900302Q00110076004900302Q00110077004900302Q00110078004900302Q00110079004900302Q0011007A004900302Q0011007B00494Q00123Q00234Q001300073Q00122Q0014007C3Q00122Q0015007D6Q00130015000200202Q0012001300494Q001300073Q00122Q0014007E3Q00122Q0015007F6Q00130015000200202Q0012001300494Q001300073Q00122Q001400803Q00122Q001500816Q00130015000200202Q00120013004900302Q00120082004900302Q0012008300494Q001300073Q00122Q001400843Q00122Q001500856Q00130015000200202Q00120013004900302Q0012008600494Q001300073Q00122Q001400873Q00122Q001500886Q0013001500020020A00012001300492Q0067001300073Q00122Q001400893Q00122Q0015008A6Q00130015000200202Q0012001300494Q001300073Q00122Q0014008B3Q00122Q0015008C6Q00130015000200202Q0012001300494Q001300073Q00122Q0014008D3Q00122Q0015008E6Q00130015000200202Q00120013004900302Q0012008F004900302Q0012009000494Q001300073Q00122Q001400913Q00122Q001500926Q00130015000200202Q0012001300494Q001300073Q00122Q001400933Q00122Q001500946Q00130015000200202Q0012001300494Q001300073Q00122Q001400953Q00122Q001500966Q00130015000200202Q0012001300494Q001300073Q00122Q001400973Q00122Q001500986Q00130015000200202Q0012001300494Q001300073Q00122Q001400993Q00122Q0015009A6Q00130015000200202Q00120013004900302Q0012009B00494Q001300073Q00122Q0014009C3Q00122Q0015009D6Q00130015000200202Q00120013004900302Q0012009E00494Q001300073Q00122Q0014009F3Q00122Q001500A06Q00130015000200202Q00120013004900302Q001200A1004900302Q001200A2004900302Q001200A300494Q001300073Q00122Q001400A43Q00122Q001500A56Q00130015000200202Q0012001300494Q001300073Q00122Q001400A63Q00122Q001500A76Q00130015000200202Q0012001300494Q001300073Q00122Q001400A83Q00122Q001500A96Q00130015000200202Q0012001300494Q001300073Q00122Q001400AA3Q00122Q001500AB6Q00130015000200202Q0012001300494Q001300073Q00122Q001400AC3Q00122Q001500AD4Q00E500130015000200201E0012001300494Q001300073Q00122Q001400AE3Q00122Q001500AF6Q00130015000200202Q0012001300494Q001300073Q00122Q001400B03Q00122Q001500B16Q00130015000200202Q0012001300494Q001300073Q00122Q001400B23Q00122Q001500B36Q00130015000200202Q0012001300494Q001300073Q00122Q001400B43Q00122Q001500B56Q00130015000200202Q0012001300494Q001300073Q00122Q001400B63Q00122Q001500B76Q00130015000200202Q0012001300494Q001300073Q00122Q001400B83Q00122Q001500B96Q00130015000200202Q0012001300494Q001300073Q00122Q001400BA3Q00122Q001500BB6Q00130015000200202Q0012001300494Q001300073Q00122Q001400BC3Q00122Q001500BD6Q00130015000200202Q0012001300494Q001300073Q00122Q001400BE3Q00122Q001500BF6Q00130015000200202Q0012001300494Q001300073Q00122Q001400C03Q00122Q001500C16Q00130015000200202Q00120013004900302Q001200C200494Q001300073Q00122Q001400C33Q00122Q001500C46Q00130015000200202Q0012001300494Q001300073Q00122Q001400C53Q00122Q001500C66Q00130015000200202Q0012001300494Q001300073Q00122Q001400C73Q00122Q001500C86Q00130015000200202Q0012001300494Q001300073Q00122Q001400C93Q00122Q001500CA6Q00130015000200202Q0012001300494Q001300073Q00122Q001400CB3Q00122Q001500CC6Q00130015000200202Q0012001300494Q001300073Q00122Q001400CD3Q00122Q001500CE4Q00E50013001500020020DB0012001300494Q001300073Q00122Q001400CF3Q00122Q001500D06Q00130015000200202Q0012001300494Q001300073Q00122Q001400D13Q00122Q001500D26Q00130015000200202Q0012001300494Q001300073Q00122Q001400D33Q00122Q001500D46Q00130015000200202Q0012001300494Q001300073Q00122Q001400D53Q00122Q001500D66Q00130015000200202Q0012001300494Q001300073Q00122Q001400D73Q00122Q001500D86Q00130015000200202Q0012001300494Q001300073Q00122Q001400D93Q00122Q001500DA6Q00130015000200202Q0012001300494Q001300073Q00122Q001400DB3Q00122Q001500DC6Q00130015000200202Q0012001300494Q001300073Q00122Q001400DD3Q00122Q001500DE6Q00130015000200202Q0012001300494Q001300073Q00122Q001400DF3Q00122Q001500E06Q00130015000200202Q0012001300494Q001300073Q00122Q001400E13Q00122Q001500E26Q00130015000200202Q0012001300494Q001300073Q00122Q001400E33Q00122Q001500E46Q00130015000200202Q0012001300494Q001300073Q00122Q001400E53Q00122Q001500E66Q00130015000200202Q0012001300494Q001300073Q00122Q001400E73Q00122Q001500E86Q00130015000200202Q0012001300494Q001300073Q00122Q001400E93Q00122Q001500EA6Q00130015000200202Q0012001300494Q001300073Q00122Q001400EB3Q00122Q001500EC6Q00130015000200202Q0012001300494Q001300073Q00122Q001400ED3Q00122Q001500EE6Q0013001500020020A00012001300492Q0014011300073Q00122Q001400EF3Q00122Q001500F06Q00130015000200202Q0012001300494Q001300073Q00122Q001400F13Q00122Q001500F26Q00130015000200202Q0012001300494Q001300073Q00122Q001400F33Q00122Q001500F46Q00130015000200202Q0012001300494Q001300073Q00122Q001400F53Q00122Q001500F66Q00130015000200202Q0012001300494Q001300073Q00122Q001400F73Q00122Q001500F86Q00130015000200202Q0012001300494Q001300073Q00122Q001400F93Q00122Q001500FA6Q00130015000200202Q0012001300494Q001300073Q00122Q001400FB3Q00122Q001500FC6Q00130015000200202Q0012001300494Q001300073Q00122Q001400FD3Q00122Q001500FE6Q00130015000200202Q0012001300494Q001300073Q00122Q001400FF3Q00122Q00152Q00015Q0013001500024Q001400016Q0012001300144Q001300073Q00122Q0014002Q012Q00122Q00150002015Q0013001500024Q001400016Q0012001300144Q001300073Q00122Q00140003012Q00122Q00150004015Q0013001500024Q001400016Q0012001300144Q001300073Q00122Q00140005012Q00122Q00150006015Q0013001500024Q001400016Q0012001300144Q001300073Q00122Q00140007012Q00122Q00150008015Q0013001500024Q001400016Q0012001300144Q001300073Q00122Q00140009012Q00122Q0015000A015Q0013001500024Q001400016Q0012001300144Q001300073Q00122Q0014000B012Q00122Q0015000C015Q0013001500022Q00FC001400014Q000C0012001300144Q001300073Q00122Q0014000D012Q00122Q0015000E015Q0013001500024Q001400016Q0012001300144Q001300073Q00122Q0014000F012Q00122Q00150010015Q0013001500024Q001400016Q00120013001400122Q00130011015Q001400016Q0012001300144Q001300073Q00122Q00140012012Q00122Q00150013015Q0013001500024Q001400016Q0012001300144Q001300073Q00122Q00140014012Q00122Q00150015015Q0013001500024Q001400016Q0012001300144Q001300073Q00122Q00140016012Q00122Q00150017015Q0013001500024Q001400016Q0012001300144Q001300073Q00122Q00140018012Q00122Q00150019015Q0013001500024Q001400016Q0012001300144Q001300073Q00122Q0014001A012Q00122Q0015001B015Q0013001500024Q001400016Q0012001300144Q001300073Q00122Q0014001C012Q00122Q0015001D015Q0013001500024Q001400016Q0012001300144Q001300073Q00122Q0014001E012Q00122Q0015001F015Q0013001500024Q001400073Q00122Q00150020012Q00122Q00160021015Q0014001600024Q001500073Q00122Q00160022012Q00122Q00170023015Q0015001700024Q001600073Q00122Q00170024012Q00122Q00180025015Q0016001800020006D700170007000100082Q0022012Q00074Q0022012Q00144Q0022012Q00154Q0022012Q00134Q0022012Q00164Q0022012Q00104Q0022012Q00114Q0022012Q00123Q001228001800463Q00122Q00190026012Q00122Q001A00463Q00122Q001B0026015Q001A001A001B00062Q001A009C020100010004D83Q009C02012Q0003011A6Q00C100180019001A001228001800463Q00122Q00190027012Q00122Q001A00463Q00122Q001B0027015Q001A001A001B00062Q001A00AA020100010004D83Q00AA0201001255001A003B4Q000E011B00073Q00122Q001C0028012Q00122Q001D0029015Q001B001D6Q001A3Q00022Q00C100180019001A001202011800463Q00122Q00190027015Q00180018001900122Q0019002A015Q00180018001900062Q001800F5020100010004D83Q00F502010012060018000F3Q0012060019002B012Q000639001800C9020100190004D83Q00C90201001255001900463Q00121D011A0027015Q00190019001A00202Q00190019003E4Q001B00073Q00122Q001C002C012Q00122Q001D002D015Q001B001D6Q00193Q000100122Q001900463Q00122Q001A0027013Q000D01190019001A0020DC00190019003E4Q001B00073Q00122Q001C002E012Q00122Q001D002F015Q001B001D6Q00193Q000100122Q00180030012Q00120600190030012Q000639001800DE020100190004D83Q00DE0201001255001900463Q0012BC001A0027015Q00190019001A00202Q0019001900434Q001B00073Q00122Q001C0031012Q00122Q001D0032015Q001B001D00020006D7001C0008000100012Q0022012Q00074Q00F90019001C000100122Q001900463Q00122Q001A0027015Q00190019001A00122Q001A002A015Q001B00016Q0019001A001B00044Q00F502010012060019000F3Q000639001800B3020100190004D83Q00B30201001255001900463Q00121D011A0027015Q00190019001A00202Q00190019003E4Q001B00073Q00122Q001C0033012Q00122Q001D0034015Q001B001D6Q00193Q000100122Q001900463Q00122Q001A0027013Q000D01190019001A0020DC00190019003E4Q001B00073Q00122Q001C0035012Q00122Q001D0036015Q001B001D6Q00193Q000100122Q0018002B012Q0004D83Q00B302010006D700180009000100012Q0022012Q00073Q0012B600180037012Q0002B80018000A3Q00125E00180038012Q00122Q001800463Q00122Q00190039012Q00122Q001A00463Q00122Q001B0039015Q001A001A001B00062Q001A0002030100010004D83Q000203012Q0003011A6Q00C100180019001A2Q004B00183Q00134Q001900073Q00122Q001A003A012Q00122Q001B003B015Q0019001B000200122Q001A003C015Q00180019001A4Q001900073Q00122Q001A003D012Q00122Q001B003E015Q0019001B000200122Q001A003F015Q00180019001A4Q001900073Q00122Q001A0040012Q00122Q001B0041015Q0019001B000200122Q001A003F015Q00180019001A4Q001900073Q00122Q001A0042012Q00122Q001B0043015Q0019001B000200122Q001A003F015Q00180019001A4Q001900073Q00122Q001A0044012Q00122Q001B0045015Q0019001B000200122Q001A0046015Q00180019001A4Q001900073Q00122Q001A0047012Q00122Q001B0048015Q0019001B000200122Q001A0046015Q00180019001A4Q001900073Q00122Q001A0049012Q00122Q001B004A015Q0019001B000200122Q001A0046015Q00180019001A4Q001900073Q00122Q001A004B012Q00122Q001B004C015Q0019001B000200122Q001A004D015Q00180019001A4Q001900073Q00122Q001A004E012Q00122Q001B004F015Q0019001B000200122Q001A0050015Q00180019001A4Q001900073Q00122Q001A0051012Q00122Q001B0052015Q0019001B000200122Q001A0053015Q00180019001A4Q001900073Q00122Q001A0054012Q00122Q001B0055015Q0019001B000200122Q001A0056015Q00180019001A4Q001900073Q00122Q001A0057012Q00122Q001B0058015Q0019001B000200122Q001A0056015Q00180019001A4Q001900073Q00122Q001A0059012Q00122Q001B005A015Q0019001B000200122Q001A005B015Q00180019001A4Q001900073Q0012AE001A005C012Q00122Q001B005D015Q0019001B000200122Q001A005B015Q00180019001A4Q001900073Q00122Q001A005E012Q00122Q001B005F015Q0019001B000200122Q001A0060013Q00CA00180019001A4Q001900073Q00122Q001A0061012Q00122Q001B0062015Q0019001B000200122Q001A0060015Q00180019001A4Q001900073Q00122Q001A0063012Q00122Q001B0064013Q00800019001B000200122Q001A0065015Q00180019001A4Q001900073Q00122Q001A0066012Q00122Q001B0067015Q0019001B000200122Q001A0068015Q00180019001A2Q004F001900073Q00122Q001A0069012Q00122Q001B006A015Q0019001B000200122Q001A006B015Q00180019001A4Q001900073Q00122Q001A006C012Q00122Q001B006D015Q0019001B0002001216001A006E015Q00180019001A4Q001900073Q00122Q001A006F012Q00122Q001B0070015Q0019001B000200122Q001A0071015Q00180019001A4Q001900073Q00122Q001A0072012Q001206001B0073013Q00E50019001B0002001206001A0074013Q00C100180019001A0006D70019000B000100022Q0022012Q00074Q0022012Q00184Q0092001A5Q00122Q001B000F3Q00122Q001C000F3Q00122Q001D00463Q00122Q001E0026015Q001D001D001E00062Q001D0094030100010004D83Q009403012Q0003011D5Q000689001D002C04013Q0004D83Q002C0401001255001E0075013Q0022011F001D4Q00A6001E000200200004D83Q002A04010012060023000F4Q0074002400243Q0012060025000F3Q0006390023009C030100250004D83Q009C030100120600250076013Q000D0124002200250006890024002A04013Q0004D83Q002A04010012060025000F4Q00740026002A3Q001206002B000F3Q000639002500C40301002B0004D83Q00C40301001206002B0077013Q003600260022002B00122Q002B0078012Q00122Q002C0079015Q002C0022002C4Q002B000200024Q002B001A002B4Q002C00013Q00062Q002B00C20301002C0004D83Q00C203012Q0074002B002B3Q00069B002600C10301002B0004D83Q00C10301001255002B00013Q00122E002C007A015Q002B002B002C4Q002C00266Q002D00073Q00122Q002E007B012Q00122Q002F007C015Q002D002F6Q002B3Q00024Q002C002C3Q00062Q002B00C20301002C0004D83Q00C203012Q00D600276Q00FC002700013Q0012060025002B012Q001206002B0030012Q000639002500EC0301002B0004D83Q00EC03010006F5002A00CD030100280004D83Q00CD03012Q0022012B00194Q0022012C00244Q00F4002B000200022Q0022012A002B3Q0006890024002A04013Q0004D83Q002A04010006890028002A04013Q0004D83Q002A0401001206002B000F3Q001206002C000F3Q000639002C00D20301002B0004D83Q00D203010006F6002900DC030100010004D83Q00DC0301001206002C007D012Q00062Q002A00030001002C0004D83Q00DC0301000689002700DE03013Q0004D83Q00DE0301001206002C002B013Q00AA001B001B002C0006F6002900E5030100010004D83Q00E50301001206002C0060012Q00062Q002A00030001002C0004D83Q00E503010006890027002A04013Q0004D83Q002A0401001206002C002B013Q00AA002C001C002C001206002D000F4Q00AA001C002C002D0004D83Q002A04010004D83Q00D203010004D83Q002A0401001206002B002B012Q000639002500A50301002B0004D83Q00A50301001255002B007E013Q0022012C00244Q00F4002B00020002000689002B000704013Q0004D83Q00070401001255002B007F013Q0095002C00073Q00122Q002D0080012Q00122Q002E0081015Q002C002E00024Q002D00246Q002B002D000200062Q002B000704013Q0004D83Q00070401001255002B007F013Q0034002C00073Q00122Q002D0082012Q00122Q002E0083015Q002C002E00024Q002D00246Q002B002D000200122Q002C003C012Q00062Q002B00040001002C0004D83Q000A04012Q0022012800273Q0004D83Q000B04012Q00D600286Q00FC002800013Q001255002B0084013Q0010012C00073Q00122Q002D0085012Q00122Q002E0086015Q002C002E6Q002B3Q000200062Q002900260401002B0004D83Q00260401001255002B0087013Q0010012C00073Q00122Q002D0088012Q00122Q002E0089015Q002C002E6Q002B3Q000200062Q002900260401002B0004D83Q00260401001255002B008A013Q00E9002C00073Q00122Q002D008B012Q00122Q002E008C015Q002C002E00024Q002D00073Q00122Q002E008D012Q00122Q002F008E015Q002D002F6Q002B3Q00024Q0029002B3Q00120600250030012Q0004D83Q00A503010004D83Q002A04010004D83Q009C030100069C001E009A030100020004D83Q009A0301001206001E0074012Q00125B001F007F015Q002000073Q00122Q0021008F012Q00122Q00220090015Q0020002200024Q002100073Q00122Q00220091012Q00122Q00230092015Q002100236Q001F3Q0002000689001F005704013Q0004D83Q00570401001255001F007F013Q0064002000073Q00122Q00210093012Q00122Q00220094015Q0020002200024Q002100073Q00122Q00220095012Q00122Q00230096015Q002100236Q001F3Q000200122Q0020003C012Q000624001F0057040100200004D83Q00570401001206001F000F4Q0074002000203Q0012060021000F3Q000639001F0048040100210004D83Q004804012Q0022012100194Q000E012200073Q00122Q00230097012Q00122Q00240098015Q002200246Q00213Q00022Q0022012000213Q0006890020005704013Q0004D83Q005704012Q0022011E00203Q0004D83Q005704010004D83Q00480401001255001F00463Q00120600200039013Q000D011F001F0020000689001F007504013Q0004D83Q00750401001206001F000F3Q0012060020000F3Q000639001F006B040100200004D83Q006B0401001255002000463Q0012BB00210039015Q00200020002100122Q00210099015Q00200021001B00122Q002000463Q00122Q00210039015Q00200020002100122Q0021009A015Q00200021001C00122Q001F002B012Q0012060020002B012Q000639001F005D040100200004D83Q005D0401001255002000463Q0012E000210039015Q00200020002100122Q0021009B015Q00200021001E00044Q007504010004D83Q005D0401001255001F00463Q0012C90020009C012Q00122Q002100463Q00122Q0022009C015Q00210021002200062Q00210082040100010004D83Q008204010012550021003B4Q000E012200073Q00122Q0023009D012Q00122Q0024009E015Q002200246Q00213Q00022Q00C1001F00200021001228001F00463Q00122Q0020009F012Q00122Q002100463Q00122Q0022009F015Q00210021002200062Q0021008B040100010004D83Q008B04012Q000301216Q00C1001F00200021001228001F00463Q00122Q002000A0012Q00122Q002100463Q00122Q002200A0015Q00210021002200062Q00210094040100010004D83Q009404012Q000301216Q00C1001F002000210006D7001F000C000100012Q0022012Q00073Q0012070120003B6Q002100073Q00122Q002200A1012Q00122Q002300A2015Q0021002300024Q002200073Q00122Q002300A3012Q00122Q002400A4015Q00220024000200122Q002300A5013Q00E50020002300020012020021000B3Q00122Q002200A6015Q0021002100224Q002200073Q00122Q002300A7012Q00122Q002400A8015Q0022002400024Q00210021002200062Q002100AD040100010004D83Q00AD0401001206002100A9012Q0012060022000F3Q0020CC0023002000434Q002500073Q00122Q002600AA012Q00122Q002700AB015Q0025002700020006D70026000D000100092Q0022012Q00224Q0022012Q00214Q0022012Q000C4Q0022012Q000D4Q0022012Q00174Q0022012Q001F4Q0022012Q00074Q0022012Q000A4Q0022012Q00194Q00010023002600012Q00CF3Q00013Q000E3Q00023Q00026Q00F03F026Q00704002264Q009F00025Q00122Q000300016Q00045Q00122Q000500013Q00042Q0003002100012Q00E300076Q00C3000800026Q000900016Q000A00026Q000B00036Q000C00046Q000D8Q000E00063Q00202Q000F000600014Q000C000F6Q000B3Q00024Q000C00036Q000D00046Q000E00016Q000F00016Q000F0006000F00102Q000F0001000F4Q001000016Q00100006001000102Q00100001001000202Q0010001000014Q000D00106Q000C8Q000A3Q000200202Q000A000A00024Q0009000A6Q00073Q000100043E0003000500012Q00E3000300054Q0022010400024Q00DA000300044Q004100036Q00CF3Q00017Q00063Q0003143Q0001AE5D8514B0438E14A559920EA7529D13AE599803043Q00DC51E21C028Q00030B3Q00426967576967734461746103083Q004D652Q736167657303063Q00536F756E647302124Q005300025Q00122Q000300013Q00122Q000400026Q00020004000200062Q00010011000100020004D83Q00110001001206000200033Q00268E00020007000100030004D83Q000700012Q00E3000300013Q00208700030003000400302Q0003000500034Q000300013Q00202Q00030003000400302Q00030006000300044Q001100010004D83Q000700012Q00CF3Q00017Q000E3Q00028Q00026Q00F03F030E3Q005F42696757696773482Q6F6B6564030E3Q00682Q6F6B73656375726566756E63030D3Q00426967576967734C6F61646572030B3Q0020D08CFFC7C200C683FCEF03063Q00A773B5E29B8A2Q0103083Q00435F412Q644F6E73030D3Q004973412Q644F6E4C6F61646564030C3Q009CFD04728AB9E73C668CACF103053Q00E3DE94632503083Q003E5741E5F834574103053Q0099532Q329600353Q0012063Q00014Q0074000100033Q00268E3Q001F000100020004D83Q001F00010006890001003400013Q0004D83Q003400010006890002003400013Q0004D83Q003400012Q00E300045Q0020E60004000400030006F600040034000100010004D83Q00340001001206000400013Q00268E0004000D000100010004D83Q000D0001001255000500043Q001217000600056Q000700013Q00122Q000800063Q00122Q000900076Q0007000900020006D700083Q000100032Q00E33Q00014Q0022012Q00034Q00E38Q00010005000800012Q00E300055Q0030500005000300080004D83Q003400010004D83Q000D00010004D83Q0034000100268E3Q0002000100010004D83Q00020001001255000400093Q00200401040004000A4Q000500013Q00122Q0006000B3Q00122Q0007000C6Q000500076Q00043Q00054Q000200056Q000100046Q00043Q00014Q000500013Q00122Q0006000D3Q00122Q0007000E6Q0005000700024Q00068Q0004000500064Q000300043Q00124Q00023Q00044Q000200012Q00CF3Q00013Q00013Q001F3Q00028Q00030F3Q00C02BE06B7276D5DD0FE24F6870C1E703073Q00A68242873C1B1103053Q007461626C6503063Q00696E7365727403083Q006D652Q736167657303093Q005043C37023504BC36503053Q0050242AAE1503073Q0047657454696D6503043Q005A152F6E03043Q001A2E705703053Q00BA2CA77BAD03083Q00D4D943CB142QDF25026Q00F03F03093Q0074696D657374616D70026Q001040031B3Q00556E697444657461696C6564546872656174536974756174696F6E03063Q00AA81A9CBBF9F03043Q00B2DAEDC803063Q00A2B4F4D7B3A103043Q00B0D6D58603053Q00636F6C6F7203063Q00FBBFB7DAAF5303073Q003994CDD6B4C836030B3Q00426967576967734461746103083Q004D652Q736167657303063Q0002E827247A1703053Q0016729D555403043Q00C6C706C103073Q00C8A4AB73A43D96027Q004002703Q001206000300014Q0074000400043Q00268E00030033000100010004D83Q003300012Q00E300055Q001206000600023Q001206000700034Q00E50005000700020006390001002C000100050004D83Q002C0001001206000500014Q0074000600093Q00268E0005000C000100010004D83Q000C00012Q00CB000A000E4Q00190009000D6Q0008000C6Q0007000B6Q0006000A3Q00122Q000A00043Q00202Q000A000A00054Q000B00013Q00202Q000B000B00064Q000C3Q00034Q000D5Q00122Q000E00073Q00122Q000F00086Q000D000F000200122Q000E00096Q000E000100024Q000C000D000E4Q000D5Q00122Q000E000A3Q00122Q000F000B6Q000D000F00024Q000C000D00084Q000D5Q00122Q000E000C3Q00122Q000F000D6Q000D000F00024Q000C000D00094Q000A000C000100044Q002C00010004D83Q000C00012Q00E3000500013Q0020C40005000500064Q000600013Q00202Q0006000600064Q000600066Q00040005000600122Q0003000E3Q00268E000300020001000E0004D83Q000200010006890004006F00013Q0004D83Q006F0001001255000500094Q001A0105000100020020E600060004000F2Q007E00050005000600264D0005006F000100100004D83Q006F0001001206000500014Q0074000600073Q00268E0005003F000100010004D83Q003F0001001255000800114Q00E400095Q00122Q000A00123Q00122Q000B00136Q0009000B00024Q000A5Q00122Q000B00143Q00122Q000C00156Q000A000C6Q00083Q00094Q000700096Q000600083Q00202Q0008000400164Q00095Q00122Q000A00173Q00122Q000B00186Q0009000B000200062Q00080058000100090004D83Q005800012Q00E3000800023Q0020E60008000800190030500008001A000E0004D83Q006F00010020E60008000400162Q003C00095Q00122Q000A001B3Q00122Q000B001C6Q0009000B000200062Q00080066000100090004D83Q006600010020E60008000400162Q005300095Q00122Q000A001D3Q00122Q000B001E6Q0009000B000200062Q0008006F000100090004D83Q006F00010006890006006F00013Q0004D83Q006F00012Q00E3000800023Q0020E60008000800190030500008001A001F0004D83Q006F00010004D83Q003F00010004D83Q006F00010004D83Q000200012Q00CF3Q00017Q000F3Q00028Q00026Q00F03F030F3Q005F5765616B41757261482Q6F6B6564030E3Q00682Q6F6B73656375726566756E63030D3Q006D7A720540A458537255157FAE03073Q002D3D16137C13CB2Q0103083Q00435F412Q644F6E73030D3Q004973412Q644F6E4C6F6164656403093Q00717F5505125368551D03053Q0053261A346E03083Q00551234555910225503043Q002638774703063Q002QE04DD8214503063Q0036938F38B645003A3Q0012063Q00014Q0074000100033Q00268E3Q001E000100020004D83Q001E00010006890001003900013Q0004D83Q003900010006890002003900013Q0004D83Q003900012Q00E300045Q0020E60004000400030006F600040039000100010004D83Q00390001001206000400013Q000E2C0001000D000100040004D83Q000D0001001255000500044Q00E3000600013Q001206000700053Q001206000800064Q00E50006000800020006D700073Q000100032Q0022012Q00034Q00E33Q00014Q00E38Q00010005000700012Q00E300055Q0030500005000300070004D83Q003900010004D83Q000D00010004D83Q0039000100268E3Q0002000100010004D83Q00020001001255000400083Q0020EC0004000400094Q000500013Q00122Q0006000A3Q00122Q0007000B6Q000500076Q00043Q00054Q000200056Q000100046Q00043Q00024Q000500013Q00122Q0006000C3Q00122Q0007000D6Q0005000700024Q00068Q0004000500064Q000500013Q00122Q0006000E3Q00122Q0007000F6Q0005000700024Q00068Q0004000500064Q000300043Q00124Q00023Q00044Q000200012Q00CF3Q00013Q00013Q00373Q00028Q0003053Q007461626C6503063Q00696E7365727403063Q00736F756E647303093Q00D51B00F01164B8CC0203073Q00D9A1726D95621003073Q0047657454696D6503053Q00012F2D72B803063Q00147240581CDC026Q00F03F031B3Q00556E697444657461696C6564546872656174536974756174696F6E03063Q00210DD3ADFDC203073Q00DD5161B2D498B003063Q00D9E60FFC1FD903053Q007AAD877D9B03093Q0074696D657374616D70026Q00104003053Q00736F756E6403093Q00BFFB348F0271E98BE403073Q00A8E4A160D95F51030E3Q00E0EB1A6A1217EFD03C5B2A43DED503063Q0037BBB14E3C4F2Q033Q000CC17A03073Q00E04DAE3F8B26AF03083Q00B0404A2981555D2A03043Q004EE42138030F3Q00EC77B543B2C779A159C5EF72B3118803053Q00E5AE1ED263030B3Q00426967576967734461746103063Q00536F756E647303113Q0039E48111DA343E08B7C666EC2F3712E38103073Q00597B8DE6318D5D030F3Q00D178F14C2743F462AC4C3146F263FB03063Q002A9311966C70030B3Q00349C1949DAA83BA73871F303063Q00886FC64D1F8703053Q003608B258A903083Q00C96269C736DD8477030F3Q00980F8C341121A5BA4CA4340B21ADAB03073Q00CCD96CE3416255027Q004003093Q0065F9C1D311807FCCD003063Q00A03EA395854C2Q033Q00F7AF2803053Q00A3B6C06D4F03083Q004D652Q736167657303083Q000F1C34F6C874052303053Q0095544660A003023Q001B2503043Q008D58666D026Q000840030A3Q008869FE46277D7EC8B05803083Q00A1D333AA107A5D3503043Q00D0A7B12303043Q00489BCED201BD3Q001206000200014Q0074000300053Q00268E0002001D000100010004D83Q001D0001001255000600023Q00207C0006000600034Q00075Q00202Q0007000700044Q00083Q00024Q000900013Q00122Q000A00053Q00122Q000B00066Q0009000B000200122Q000A00076Q000A000100024Q00080009000A4Q000900013Q00122Q000A00083Q00122Q000B00096Q0009000B00024Q000800096Q0006000800014Q00065Q00202Q0006000600044Q00075Q00202Q0007000700044Q000700076Q00030006000700122Q0002000A3Q00268E000200020001000A0004D83Q000200010012550006000B4Q0081000700013Q00122Q0008000C3Q00122Q0009000D6Q0007000900024Q000800013Q00122Q0009000E3Q00122Q000A000F6Q0008000A6Q00063Q00074Q000500076Q000400063Q00062Q000300BC00013Q0004D83Q00BC0001001255000600074Q001A0106000100020020E60007000300102Q007E00060006000700264D000600BC000100110004D83Q00BC00010020E60006000300122Q003C000700013Q00122Q000800133Q00122Q000900146Q00070009000200062Q00060056000100070004D83Q005600010020E60006000300122Q003C000700013Q00122Q000800153Q00122Q000900166Q00070009000200062Q00060056000100070004D83Q005600010020E60006000300122Q003C000700013Q00122Q000800173Q00122Q000900186Q00070009000200062Q00060056000100070004D83Q005600010020E60006000300122Q003C000700013Q00122Q000800193Q00122Q0009001A6Q00070009000200062Q00060056000100070004D83Q005600010020E60006000300122Q0053000700013Q00122Q0008001B3Q00122Q0009001C6Q00070009000200062Q0006005A000100070004D83Q005A00012Q00E3000600023Q0020E600060006001D0030500006001E000A0004D83Q00BC00010020E60006000300122Q003C000700013Q00122Q0008001F3Q00122Q000900206Q00070009000200062Q00060081000100070004D83Q008100010020E60006000300122Q003C000700013Q00122Q000800213Q00122Q000900226Q00070009000200062Q00060081000100070004D83Q008100010020E60006000300122Q003C000700013Q00122Q000800233Q00122Q000900246Q00070009000200062Q00060081000100070004D83Q008100010020E60006000300122Q003C000700013Q00122Q000800253Q00122Q000900266Q00070009000200062Q00060081000100070004D83Q008100010020E60006000300122Q0053000700013Q00122Q000800273Q00122Q000900286Q00070009000200062Q00060085000100070004D83Q008500010006890004008100013Q0004D83Q0081000100264D000500850001000A0004D83Q008500012Q00E3000600023Q0020E600060006001D0030500006001E00290004D83Q00BC00010020E60006000300122Q003C000700013Q00122Q0008002A3Q00122Q0009002B6Q00070009000200062Q00060093000100070004D83Q009300010020E60006000300122Q0053000700013Q00122Q0008002C3Q00122Q0009002D6Q00070009000200062Q00060097000100070004D83Q009700012Q00E3000600023Q0020E600060006001D0030500006002E000A0004D83Q00BC00010020E60006000300122Q003C000700013Q00122Q0008002F3Q00122Q000900306Q00070009000200062Q000600A5000100070004D83Q00A500010020E60006000300122Q0053000700013Q00122Q000800313Q00122Q000900326Q00070009000200062Q000600A9000100070004D83Q00A900012Q00E3000600023Q0020E600060006001D0030500006001E00330004D83Q00BC00010020E60006000300122Q003C000700013Q00122Q000800343Q00122Q000900356Q00070009000200062Q000600B7000100070004D83Q00B700010020E60006000300122Q0053000700013Q00122Q000800363Q00122Q000900376Q00070009000200062Q000600BC000100070004D83Q00BC00012Q00E3000600023Q0020E600060006001D0030500006001E00110004D83Q00BC00010004D83Q000200012Q00CF3Q00017Q000C3Q00028Q0003083Q00435F412Q644F6E73030D3Q004973412Q644F6E4C6F61646564030C3Q00FE84ED46EDD995FE5DD6D98F03053Q00BFB6E19F29030C3Q004865726F526F746174696F6E03123Q005F4D794C6567656E64617279482Q6F6B6564030E3Q00682Q6F6B73656375726566756E6303093Q004E616D65706C61746503073Q000A162C7C2Q88CC03073Q00A24B724835EBE72Q0100293Q0012063Q00014Q0074000100023Q000E2C0001000200013Q0004D83Q00020001001255000300023Q0020520003000300034Q00045Q00122Q000500043Q00122Q000600056Q000400066Q00033Q00044Q000200046Q000100033Q00062Q0001002800013Q0004D83Q002800010006890002002800013Q0004D83Q00280001001255000300064Q00E3000400013Q0020E60004000400070006F600040028000100010004D83Q00280001001206000400013Q00268E00040017000100010004D83Q00170001001255000500083Q0020A20006000300094Q00075Q00122Q0008000A3Q00122Q0009000B6Q0007000900020006D700083Q000100012Q00E33Q00014Q00010005000800012Q00E3000500013Q00305000050007000C0004D83Q002800010004D83Q001700010004D83Q002800010004D83Q000200012Q00CF3Q00013Q00013Q00063Q0003063Q00556E6974494403063Q0048724461746103053Q00546F6B656E03063Q00737472696E6703053Q006C6F7765720002113Q0006893Q000D00013Q0004D83Q000D00010020E600023Q00010006890002000D00013Q0004D83Q000D00012Q00E300025Q00205100020002000200122Q000300043Q00202Q00030003000500202Q00043Q00014Q00030002000200102Q00020003000300044Q001000012Q00E300025Q0020E60002000200020030500002000300062Q00CF3Q00017Q000B3Q00028Q0003083Q00435F412Q644F6E73030D3Q004973412Q644F6E4C6F61646564030C3Q00A43956ED610D983D50EB5C0C03063Q0062EC5C248233030C3Q004865726F526F746174696F6E030B3Q005F54657874482Q6F6B6564030E3Q00682Q6F6B73656375726566756E63030D3Q0087181FAE64A6BB3FB02Q18BF4103083Q0050C4796CDA25C8D52Q0100293Q0012063Q00014Q0074000100023Q00268E3Q0002000100010004D83Q00020001001255000300023Q0020520003000300034Q00045Q00122Q000500043Q00122Q000600056Q000400066Q00033Q00044Q000200046Q000100033Q00062Q0001002800013Q0004D83Q002800010006890002002800013Q0004D83Q00280001001255000300064Q00E3000400013Q0020E60004000400070006F600040028000100010004D83Q00280001001206000400013Q00268E00040017000100010004D83Q00170001001255000500084Q0099000600036Q00075Q00122Q000800093Q00122Q0009000A6Q0007000900020006D700083Q000100012Q00E33Q00014Q00010005000800012Q00E3000500013Q00305000050007000B0004D83Q002800010004D83Q001700010004D83Q002800010004D83Q000200012Q00CF3Q00013Q00013Q00023Q0003063Q0048724461746103083Q00436173745465787405044Q00E300055Q0020E60005000500010010260005000200022Q00CF3Q00017Q000C3Q00028Q00026Q00F03F03083Q00556E69744175726103053Q007063612Q6C026Q005E4003063Q0073656C65637403013Q002303083Q00417572615574696C03043Q0074797065030B3Q00466F72456163684175726103083Q0006660C7C5F07850E03073Q00EA6013621F2B6E02443Q001206000300014Q0074000400053Q00268E00030023000100020004D83Q00230001001206000500023Q001255000600034Q009100078Q000800056Q000900016Q00060009000F00062Q0006000D000100010004D83Q000D00010004D83Q00430001001255001000044Q000B011100046Q001200066Q001300076Q001400086Q001500096Q0016000A6Q0017000B6Q0018000C6Q0019001A6Q001B000F6Q0010001B001100062Q0010001C000100010004D83Q001C00010004D83Q0043000100201F00120005000200201F000500120001000EDE00050005000100050004D83Q000500010004D83Q004300010004D83Q000500010004D83Q0043000100268E00030002000100010004D83Q00020001001255000600063Q002Q12010700063Q00122Q000800076Q00098Q00073Q00024Q00088Q00063Q00024Q000400063Q00122Q000600083Q00062Q0006004100013Q0004D83Q00410001001255000600093Q001271000700083Q00202Q00070007000A4Q0006000200024Q00075Q00122Q0008000B3Q00122Q0009000C6Q00070009000200062Q00060041000100070004D83Q00410001001255000600083Q00203800060006000A4Q00078Q000800016Q00098Q00068Q00065Q001206000300023Q0004D83Q000200012Q00CF3Q00017Q008B3Q0003183Q004C6567656E6461727953652Q74696E6773436C612Q73696303083Q0053652Q74696E6773030B3Q000F8EB7540E8B85421F82B603043Q00246BE7C4027Q004003043Q006D61746803063Q0072616E646F6D026Q00F0BF026Q00F03F028Q0003123Q004765744E756D47726F75704D656D62657273026Q00394003093Q00556E6974436C612Q7303063Q004DB9A39E58A703043Q00E73DD5C203143Q00435F5370656369616C697A6174696F6E496E666F03113Q004765745370656369616C697A6174696F6E03153Q004765745370656369616C697A6174696F6E496E666F030D3Q004973506C617965725370652Q6C024Q00A0D71741024Q0010140A4103073Q002DA42E7608BE3803043Q001369CD5D024Q00DC051641024Q004450164103063Q009907D79230A703053Q005FC968BEE1024Q002019094103053Q0082CAC6C7AC03043Q00AECFABA1025Q00F5094103063Q00DDF104E0F7D903063Q00B78D9E6D939803073Q000800F5092D1AE303043Q006C4C6986026Q000840025Q00BCA54003053Q00C8D0A3F2CB03053Q00AE8BA5D181024Q0028BC1741025Q00FD174103063Q0093BCEBD2C90D03083Q0018C3D382A1A6631003073Q00620AFA2952054303063Q00762663894C33024Q00A0A10A41024Q0060140A4103073Q00D92F16170833F803063Q00409D4665726903063Q0070A7AEF01F4E03053Q007020C8C783024Q00A0601741024Q00C055E94003053Q000F454EABC603073Q00424C303CD8A3CB03063Q00737472696E6703053Q00752Q70657203013Q003A03113Q009EB44CDA7B94169FB54DDC6DEF1093A95703073Q0044DAE619933FAE03123Q009E0272619783706169859905616D8284057D03053Q00D6CD4A332C030B3Q00CA7ECBD944CE16CAD35BC303053Q00179A2C829C03113Q002194848B05274B82849D153A218A84801303063Q007371C6CDCE56030F3Q00A978D071DE7AD769B060DB7BB272CC03043Q003AE4379E03133Q0091BFFF05199F6F84BBF51D199F0395BDF9011203073Q0055D4E9B04E5CCD030C3Q007A79A4C36E71A6B86277A4DB03043Q00822A38E803053Q00C7B423EA4303063Q005F8AD544832003043Q0004078F6603053Q00164A48C12303063Q00045CC574094B03043Q00384C198403053Q0073C0AC2FCC03053Q00AF3EA1CB46024Q00E8F2174103053Q001FC8D1003003053Q00555CBDA37303063Q0019A3392B26A203043Q005849CC50025Q00B07D4003053Q000D9602552C03063Q00BA4EE3702649025Q00EDF54003053Q00D156FA5C5003063Q001A9C379D353303063Q009CD417C0BD4203063Q0030ECB876B9D8026Q00144003053Q00F5BC4524D603063Q005485DD3750AF03043Q00AFE62DA203063Q003CDD8744C6A7030C3Q00C69CCAAE64ECC2A1CAA26BFD03063Q00B98EDD98E32203053Q007461626C6503043Q00736F727403163Q00556E697447726F7570526F6C6573412Q7369676E656403043Q00756E697403043Q003C1D346B03073Q009D685C7A20646D03043Q0097872QE103083Q00CBC3C6AFAA5D47ED03063Q003E473FCC542Q03073Q009C4E2B5EB53171026Q00594003083Q00746F6E756D62657203053Q006D617463682Q033Q0037EC8F03073Q00191288A4C36B2303043Q0066696E6403043Q00FA2CA04B03083Q00D8884DC92F12DCA103093Q00B5D26311B75B6E23AA03083Q0046D8BD1662D2341803063Q00CEDEB180D6CE03053Q00B3BABFC3E703063Q0069706169727303063Q00ED3E0AE3FC2B03043Q0084995F7803063Q00A5B31C2AF2CE03073Q00C0D1D26E4D97BA025Q00C0724003093Q00ED0C372QFACBF6063003063Q00A4806342899F03093Q000D86FCAD0586FFBB1203043Q00DE60E989026Q00694003023Q005F47030D3Q004C44697370656C43616368654C03093Q00BEA1A80A98C6FEB0A703073Q0090D9D3C77FE893030A3Q00FB3A2D3CDA48374AF13B03083Q0024984F5E48B525620001022Q0012613Q00013Q00206Q00024Q00015Q00122Q000200033Q00122Q000300046Q0001000300028Q000100064Q000A000100010004D83Q000A00010012063Q00053Q001255000100063Q00209700010001000700122Q000200083Q00122Q000300096Q0001000300028Q000100122Q0001000A3Q00122Q0002000B6Q00020001000200262Q000200170001000A0004D83Q00170001001206000100093Q0004D83Q001800012Q00222Q0100023Q000EDE000C001B000100010004D83Q001B00010012060001000C3Q0012550003000D4Q001C01045Q00122Q0005000E3Q00122Q0006000F6Q000400066Q00033Q000500122Q000600103Q00202Q0006000600114Q0006000100024Q000700083Q00062Q0006003200013Q0004D83Q00320001001255000900103Q0020470009000900124Q000A00066Q00090002000E4Q0008000E6Q0005000D6Q0005000C6Q0005000B6Q0007000A6Q000500093Q00044Q003300012Q00CF3Q00013Q0006890007002A2Q013Q0004D83Q002A2Q010006890004002A2Q013Q0004D83Q002A2Q010012060009000A4Q0074000A000A3Q00268E00090073000100050004D83Q00730001001255000B00133Q001206000C00144Q00F4000B000200020006F6000B0045000100010004D83Q00450001001255000B00133Q001206000C00154Q00F4000B00020002000689000B004A00013Q0004D83Q004A00012Q00E3000B5Q001206000C00163Q001206000D00174Q00E5000B000D00022Q0017010B00013Q001255000B00133Q001206000C00184Q00F4000B000200020006F6000B0054000100010004D83Q00540001001255000B00133Q001206000C00194Q00F4000B00020002000689000B005900013Q0004D83Q005900012Q00E3000B5Q001206000C001A3Q001206000D001B4Q00E5000B000D00022Q0017010B00023Q001255000B00133Q001206000C001C4Q00F4000B00020002000689000B006300013Q0004D83Q006300012Q00E3000B5Q001206000C001D3Q001206000D001E4Q00E5000B000D00022Q0017010B00033Q001255000B00133Q001206000C001F4Q00F4000B00020002000689000B007200013Q0004D83Q007200012Q00E3000B5Q00123D000C00203Q00122Q000D00216Q000B000D00024Q000C5Q00122Q000D00223Q00122Q000E00236Q000C000E00024Q000C00016Q000B00023Q001206000900243Q000E2C000900B7000100090004D83Q00B70001001255000B00133Q001206000C00254Q00F4000B00020002000689000B007F00013Q0004D83Q007F00012Q00E3000B5Q001206000C00263Q001206000D00274Q00E5000B000D00022Q0017010B00043Q001255000B00133Q001206000C00284Q00F4000B000200020006F6000B0089000100010004D83Q00890001001255000B00133Q001206000C00294Q00F4000B00020002000689000B009300013Q0004D83Q009300012Q00E3000B5Q00123D000C002A3Q00122Q000D002B6Q000B000D00024Q000C5Q00122Q000D002C3Q00122Q000E002D6Q000C000E00024Q000C00016Q000B00023Q001255000B00133Q001206000C002E4Q00F4000B000200020006F6000B009D000100010004D83Q009D0001001255000B00133Q001206000C002F4Q00F4000B00020002000689000B00A700013Q0004D83Q00A700012Q00E3000B5Q00123D000C00303Q00122Q000D00316Q000B000D00024Q000C5Q00122Q000D00323Q00122Q000E00336Q000C000E00024Q000C00026Q000B00013Q001255000B00133Q001206000C00344Q00F4000B000200020006F6000B00B1000100010004D83Q00B10001001255000B00133Q001206000C00354Q00F4000B00020002000689000B00B600013Q0004D83Q00B600012Q00E3000B5Q001206000C00363Q001206000D00374Q00E5000B000D00022Q0017010B00043Q001206000900053Q00268E000900122Q01000A0004D83Q00122Q01001255000B00383Q002075000B000B00394Q000C00043Q00122Q000D003A6Q000E00076Q000C000C000E4Q000B000200024Q000A000B6Q000B5Q00122Q000C003B3Q00122Q000D003C6Q000B000D000200062Q000A00EB0001000B0004D83Q00EB00012Q00E3000B5Q001206000C003D3Q001206000D003E4Q00E5000B000D000200069B000A00EB0001000B0004D83Q00EB00012Q00E3000B5Q001206000C003F3Q001206000D00404Q00E5000B000D000200069B000A00EB0001000B0004D83Q00EB00012Q00E3000B5Q001206000C00413Q001206000D00424Q00E5000B000D000200069B000A00EB0001000B0004D83Q00EB00012Q00E3000B5Q001206000C00433Q001206000D00444Q00E5000B000D000200069B000A00EB0001000B0004D83Q00EB00012Q00E3000B5Q001206000C00453Q001206000D00464Q00E5000B000D000200069B000A00EB0001000B0004D83Q00EB00012Q00E3000B5Q001206000C00473Q001206000D00484Q00E5000B000D0002000639000A00F00001000B0004D83Q00F000012Q00E3000B5Q001206000C00493Q001206000D004A4Q00E5000B000D00022Q0017010B00034Q00E3000B00034Q0053000C5Q00122Q000D004B3Q00122Q000E004C6Q000C000E000200062Q000B00022Q01000C0004D83Q00022Q012Q00E3000B5Q001206000C004D3Q001206000D004E4Q00E5000B000D0002000639000800022Q01000B0004D83Q00022Q012Q00E3000B5Q001206000C004F3Q001206000D00504Q00E5000B000D00022Q0017010B00033Q001255000B00133Q001206000C00514Q00F4000B00020002000689000B00112Q013Q0004D83Q00112Q012Q00E3000B5Q00123D000C00523Q00122Q000D00536Q000B000D00024Q000C5Q00122Q000D00543Q00122Q000E00556Q000C000E00024Q000C00026Q000B00043Q001206000900093Q00268E00090039000100240004D83Q00390001001255000B00133Q001206000C00564Q00F4000B00020002000689000B001E2Q013Q0004D83Q001E2Q012Q00E3000B5Q001206000C00573Q001206000D00584Q00E5000B000D00022Q0017010B00043Q001255000B00133Q001206000C00594Q00F4000B00020002000689000B002A2Q013Q0004D83Q002A2Q012Q00E3000B5Q001222000C005A3Q00122Q000D005B6Q000B000D00024Q000B00033Q00044Q002A2Q010004D83Q003900010002B800096Q00D4000A5Q00122Q000B000A3Q00202Q000C0001000900122Q000D00093Q00042Q000B00632Q01001206000F000A4Q0074001000103Q00268E000F00322Q01000A0004D83Q00322Q0100268E000E003C2Q01000A0004D83Q003C2Q012Q00E300115Q0012060012005C3Q0012060013005D4Q00E50011001300020006EA0010004C2Q0100110004D83Q004C2Q0100264D000100462Q01005E0004D83Q00462Q012Q00E300115Q0012160112005F3Q00122Q001300606Q0011001300024Q0012000E6Q00110011001200062Q0010004C2Q0100110004D83Q004C2Q012Q00E300115Q00127A001200613Q00122Q001300626Q0011001300024Q0012000E6Q0010001100122Q00E3001100054Q006B001200106Q00135Q00122Q001400633Q00122Q001500646Q0013001500024Q001400143Q0006D7001500010001000A2Q00E33Q00064Q00E33Q00034Q00E33Q00024Q00E33Q00014Q00E33Q00044Q0022017Q0022012Q00094Q0022012Q00104Q00E38Q0022012Q000A4Q00010011001500010004D83Q00612Q010004D83Q00322Q012Q00C7000F5Q00043E000B00302Q01001255000B00653Q0020E6000B000B00662Q0022010C000A3Q0002B8000D00024Q0001000B000D00012Q0074000B000B4Q008C000C000A3Q000EDE000A008E2Q01000C0004D83Q008E2Q01001255000C00673Q002013000D000A000900202Q000D000D00684Q000C000200024Q000D5Q00122Q000E00693Q00122Q000F006A6Q000D000F000200062Q000C007C2Q01000D0004D83Q007C2Q012Q008C000C000A3Q00268E000C007C2Q0100090004D83Q007C2Q010020E6000C000A00090020E6000B000C00680004D83Q008E2Q01001255000C00673Q002093000D000A000900202Q000D000D00684Q000C000200024Q000D5Q00122Q000E006B3Q00122Q000F006C6Q000D000F000200062Q000C00892Q01000D0004D83Q00892Q010020E6000C000A00090020E6000B000C00680004D83Q008E2Q012Q008C000C000A3Q000EDE0009008E2Q01000C0004D83Q008E2Q010020E6000C000A00050020E6000B000C0068001206000C000A3Q000689000B00B92Q013Q0004D83Q00B92Q012Q00E3000D5Q001206000E006D3Q001206000F006E4Q00E5000D000F0002000639000B00992Q01000D0004D83Q00992Q01001206000C006F3Q0004D83Q00B92Q01001206000D000A4Q0074000E000E3Q00268E000D009B2Q01000A0004D83Q009B2Q01001255000F00703Q001209001000383Q00202Q0010001000714Q0011000B6Q00125Q00122Q001300723Q00122Q001400736Q001200146Q00108Q000F3Q00024Q000E000F3Q00062Q000E00B92Q013Q0004D83Q00B92Q01001255000F00383Q002019010F000F00744Q0010000B6Q00115Q00122Q001200753Q00122Q001300766Q001100136Q000F3Q000200062Q000F00B62Q013Q0004D83Q00B62Q012Q0022010C000E3Q0004D83Q00B92Q012Q0022010C000E3Q0004D83Q00B92Q010004D83Q009B2Q010006D7000D0003000100072Q00E33Q00074Q00E38Q00E33Q00054Q00E33Q00034Q00E33Q00024Q00E33Q00014Q00E33Q00043Q00121F010E000A6Q000F00016Q00105Q00122Q001100773Q00122Q001200786Q0010001200024Q00115Q00122Q001200793Q00122Q0013007A6Q001100136Q000F3Q00010012550010007B4Q00220111000F4Q00A60010000200120004D83Q00F12Q012Q00E300155Q0012060016007C3Q0012060017007D4Q00E5001500170002000639001400E12Q0100150004D83Q00E12Q0100268E000E00F12Q01000A0004D83Q00F12Q012Q00220115000D4Q00F300165Q00122Q0017007E3Q00122Q0018007F6Q00160018000200122Q001700806Q0015001700024Q000E00153Q0004D83Q00F12Q012Q00E300155Q001206001600813Q001206001700824Q00E5001500170002000639001400F12Q0100150004D83Q00F12Q0100268E000E00F12Q01000A0004D83Q00F12Q012Q00220115000D4Q00F300165Q00122Q001700833Q00122Q001800846Q00160018000200122Q001700856Q0015001700024Q000E00153Q00069C001000D02Q0100020004D83Q00D02Q01001255001000864Q00AB00113Q00024Q00125Q00122Q001300883Q00122Q001400896Q0012001400024Q00110012000C4Q00125Q00122Q0013008A3Q00122Q0014008B6Q0012001400024Q00110012000E00102Q0010008700116Q00013Q00043Q00053Q00028Q00030A3Q00556E6974457869737473026Q00F03F030A3Q00556E69744865616C7468030D3Q00556E69744865616C74684D617801273Q001206000100014Q0074000200023Q00268E00010021000100010004D83Q00210001001255000300024Q002201046Q00F40003000200022Q0022010200033Q0006890002002000013Q0004D83Q00200001001206000300014Q0074000400053Q00268E00030010000100030004D83Q001000012Q000F0006000400052Q0018010600023Q00268E0003000C000100010004D83Q000C0001001255000600044Q002201076Q00F40006000200020006EA00040018000100060004D83Q00180001001206000400013Q001255000600054Q002201076Q00F40006000200020006EA0005001E000100060004D83Q001E0001001206000500033Q001206000300033Q0004D83Q000C0001001206000100033Q00268E00010002000100030004D83Q00020001001206000300014Q0018010300023Q0004D83Q000200012Q00CF3Q00017Q000C3Q00024Q00E4DF1A41028Q0003073Q0047657454696D65030B3Q00556E6974496E52616E676503063Q0048C956E3462103073Q009738A5379A235303053Q007461626C6503063Q00696E7365727403043Q00B54D0CFA03043Q008EC0236503063Q00DE7028AFF38403083Q0076B61549C387ECCC0A4A4Q00E3000B6Q000D010B000B00090006F6000B0012000100010004D83Q001200010006890003001200013Q0004D83Q001200012Q00E3000B00013Q00069B000300140001000B0004D83Q001400012Q00E3000B00023Q00069B000300140001000B0004D83Q001400012Q00E3000B00033Q00069B000300140001000B0004D83Q001400012Q00E3000B00043Q00069B000300140001000B0004D83Q0014000100268E00090049000100010004D83Q00490001001206000B00024Q0074000C000C3Q00268E000B0016000100020004D83Q00160001001255000D00034Q0009010D000100024Q000C0005000D4Q000D00056Q000D0004000D00062Q000C00490001000D0004D83Q00490001001206000D00024Q0074000E000E3Q000E2C000200210001000D0004D83Q002100012Q00E3000F00064Q00E3001000074Q00F4000F000200022Q0022010E000F3Q000EDE000200490001000E0004D83Q00490001001255000F00044Q00E3001000074Q00F4000F000200020006F6000F0035000100010004D83Q003500012Q00E3000F00074Q0053001000083Q00122Q001100053Q00122Q001200066Q00100012000200062Q000F0049000100100004D83Q00490001001255000F00073Q002079000F000F00084Q001000096Q00113Q00024Q001200083Q00122Q001300093Q00122Q0014000A6Q0012001400024Q001300076Q0011001200134Q001200083Q00122Q0013000B3Q00122Q0014000C6Q0012001400024Q00110012000E4Q000F0011000100044Q004900010004D83Q002100010004D83Q004900010004D83Q001600012Q00CF3Q00017Q00013Q0003063Q006865616C746802083Q0020E600023Q00010020E600030001000100066C00020005000100030004D83Q000500012Q00D600026Q00FC000200014Q0018010200024Q00CF3Q00017Q000A3Q00028Q00026Q00F03F03083Q00556E69744E616D6500030C3Q00556E69744973467269656E6403063Q003DE02AC30DCE03073Q00E24D8C4BBA68BC2Q01030C3Q0091EFE212698CE2CC0D6E90EA03053Q002FD9AEB05F02353Q001206000200014Q0074000300033Q00268E00020006000100020004D83Q00060001001206000400014Q0018010400023Q00268E00020002000100010004D83Q00020001001255000400034Q002201056Q00F40004000200022Q0022010300043Q00264E00030032000100040004D83Q003200012Q00E300046Q000D0104000400030006F600040032000100010004D83Q00320001001206000400014Q0074000500053Q00268E00040014000100010004D83Q00140001001255000600054Q002A000700013Q00122Q000800063Q00122Q000900076Q0007000900024Q00088Q0006000800024Q000500063Q00262Q00050032000100040004D83Q0032000100268E00050032000100080004D83Q003200012Q00E3000600024Q006B00078Q000800013Q00122Q000900093Q00122Q000A000A6Q0008000A00024Q000900093Q0006D7000A3Q000100052Q00E33Q00034Q00E33Q00044Q00E33Q00054Q00E33Q00064Q0022012Q00014Q00010006000A00010004D83Q003200010004D83Q00140001001206000200023Q0004D83Q000200012Q00CF3Q00013Q00017Q000A113Q0006890003001000013Q0004D83Q001000012Q00E3000B5Q00069B0003000E0001000B0004D83Q000E00012Q00E3000B00013Q00069B0003000E0001000B0004D83Q000E00012Q00E3000B00023Q00069B0003000E0001000B0004D83Q000E00012Q00E3000B00033Q000639000300100001000B0004D83Q001000012Q00E3000B00044Q0018010B00024Q00CF3Q00017Q000C3Q0003153Q00B88DC8FB51BA9ECCEC40AD93C0EC53B796C6F058AC03053Q0014E8C189A203173Q000EF0E482CEA2304E11FCF783C2A228550BECE484CBA93303083Q001142BFA5C687EC7703023Q005F4703143Q006E616D65706C6174654C556E697473436163686503153Q00218E8336C0D8C0F03B8A9126D1C1D8EE2E8B8A36DB03083Q00B16FCFCE739F888C031F3Q0048616E646C654C4E616D65706C617465556E6974734361636865412Q64656403173Q002BA83D31EB7F7324BD352BE1617631B62231F9606920AD03073Q003F65E97074B42F03213Q0048616E646C654C4E616D65706C617465556E697473436163686552656D6F76656403284Q003C00045Q00122Q000500013Q00122Q000600026Q00040006000200062Q0001000C000100040004D83Q000C00012Q00E300045Q001206000500033Q001206000600044Q00E500040006000200063900010010000100040004D83Q00100001001255000400054Q000301055Q0010260004000600050004D83Q002700012Q00E300045Q001206000500073Q001206000600084Q00E50004000600020006390001001C000100040004D83Q001C00010006890002002700013Q0004D83Q00270001001255000400094Q0022010500024Q009A0004000200010004D83Q002700012Q00E300045Q0012060005000A3Q0012060006000B4Q00E500040006000200063900010027000100040004D83Q002700010006890002002700013Q0004D83Q002700010012550004000C4Q0022010500024Q009A0004000200012Q00CF3Q00017Q00183Q00028Q00030B3Q00435F4E616D65506C61746503133Q004765744E616D65506C617465466F72556E6974026Q00F03F03083Q00556E69744755494403083Q0073747273706C697403013Q002D027Q0040030A3Q00AAF188EA128FFA80EC2903053Q005DED90E58F03073Q0023F3F810084A1003063Q0026759690796B03023Q005F4703143Q006E616D65706C6174654C556E697473436163686503093Q0038B5E72E1DB7EF2E2803043Q005A4DDB8E03083Q00F30A282D620677E303073Q001A866441592C6703083Q00E4ED393783C4CA1403053Q00C49183504303063Q000BBE0F1C31EC03063Q00887ED066687803123Q006E616D65506C617465556E6974546F6B656E03083Q00556E69744E616D6501533Q001206000100014Q0074000200023Q00268E00010002000100010004D83Q00020001001255000300023Q002Q200003000300034Q00048Q000500016Q0003000500024Q000200033Q00062Q0002005200013Q0004D83Q00520001001206000300014Q0074000400093Q00268E00030020000100040004D83Q00200001001255000A00054Q00B7000B00046Q000A000200024Q0006000A3Q00122Q000A00063Q00122Q000B00076Q000C00066Q000A000C00104Q000800106Q0009000F6Q0008000E6Q0008000D6Q0008000C6Q0008000B6Q0007000A3Q00122Q000300083Q00268E00030047000100080004D83Q004700012Q00E3000A5Q001206000B00093Q001206000C000A4Q00E5000A000C00020006390007002E0001000A0004D83Q002E00012Q00E3000A5Q001206000B000B3Q001206000C000C4Q00E5000A000C000200069B000700520001000A0004D83Q00520001001255000A000D3Q0020E1000A000A000E4Q000B3Q00044Q000C5Q00122Q000D000F3Q00122Q000E00106Q000C000E00024Q000B000C00044Q000C5Q00122Q000D00113Q00122Q000E00126Q000C000E00024Q000B000C00054Q000C5Q00122Q000D00133Q00122Q000E00146Q000C000E00024Q000B000C00064Q000C5Q00122Q000D00153Q00122Q000E00166Q000C000E00024Q000B000C00094Q000A0004000B00044Q0052000100268E0003000E000100010004D83Q000E00010020E600040002001700120C010A00186Q000B00046Q000A000200024Q0005000A3Q00122Q000300043Q00044Q000E00010004D83Q005200010004D83Q000200012Q00CF3Q00017Q00033Q0003023Q005F4703143Q006E616D65706C6174654C556E69747343616368650001093Q001255000100013Q0020E60001000100022Q000D2Q0100013Q00264E00010008000100030004D83Q00080001001255000100013Q0020E60001000100020020A000013Q00032Q00CF3Q00017Q00273Q00028Q00027Q0040026Q000840026Q005940030C3Q00556E69745265616374696F6E03063Q00EFECB3A00D2C03063Q005E9F80D2D96803063Q0040F507A65A6D03083Q001A309966DF3F1F99026Q001040026Q00F03F03073Q00435F5370652Q6C030C3Q004765745370652Q6C496E666F025Q00C0524003043Q006E616D6500030E3Q0049735370652Q6C496E52616E676503053Q007370652Q6C03043Q000C41E0F603043Q009362208D03043Q000A42EDC103073Q002B782383AA663603043Q005D0588B803073Q00E43466E7D6C5D003083Q001DE1662QDE8214D303083Q00B67E8015AA8AEB7903083Q0086D33BD4871D372Q03083Q0066EBBA5586E6735003083Q005A0D266D73DA255203073Q0042376C5E3F12B403073Q00079D803B2B703003063Q003974EDE55747030C3Q00A5A3E4E07EE046A698EEE87903073Q0027CAD18D87178E026Q0020402Q0103053Q00706169727303063Q00435F4974656D030D3Q0049734974656D496E52616E676501A43Q001206000100014Q0074000200053Q00268E00010007000100020004D83Q000700012Q0074000400044Q00FC000500013Q001206000100033Q00268E0001001F000100010004D83Q001F0001001206000200043Q0012A8000600056Q00075Q00122Q000800063Q00122Q000900076Q0007000900024Q00088Q00060008000200062Q0006001D00013Q0004D83Q001D0001001255000600054Q005700075Q00122Q000800083Q00122Q000900096Q0007000900024Q00088Q00060008000200262Q0006001D0001000A0004D83Q001D00010004D83Q001E00012Q0018010200023Q0012060001000B3Q00268E0001008B000100030004D83Q008B00010006890005003A00013Q0004D83Q003A0001001206000600013Q00268E00060024000100010004D83Q002400010012550007000C3Q0020B000070007000D00122Q0008000E6Q0007000200024Q000300073Q00202Q00070003000F00262Q00070035000100100004D83Q003500010012550007000C3Q00204300070007001100202Q00080003000F4Q00098Q0007000900024Q000400073Q00044Q008500012Q00D600046Q00FC000400013Q0004D83Q008500010004D83Q002400010004D83Q00850001001206000600014Q00740007000E3Q00268E00060074000100010004D83Q00740001001255000F000D3Q0012F7001000126Q000F000200164Q000E00166Q000D00156Q000C00146Q000B00136Q000A00126Q000900116Q000800106Q0007000F6Q000F3Q00084Q00105Q00122Q001100133Q00122Q001200146Q0010001200024Q000F001000074Q00105Q00122Q001100153Q00122Q001200166Q0010001200024Q000F001000084Q00105Q00122Q001100173Q00122Q001200186Q0010001200024Q000F001000094Q00105Q00122Q001100193Q00122Q0012001A6Q0010001200024Q000F0010000A4Q00105Q00122Q0011001B3Q00122Q0012001C6Q0010001200024Q000F0010000B4Q00105Q00122Q0011001D3Q00122Q0012001E6Q0010001200024Q000F0010000C4Q00105Q00122Q0011001F3Q00122Q001200206Q0010001200024Q000F0010000D4Q00105Q00122Q001100213Q00122Q001200226Q0010001200024Q000F0010000E4Q0003000F3Q00122Q0006000B3Q000E2C000B003C000100060004D83Q003C00010020E6000F0003000F00264E000F0082000100100004D83Q00820001001255000F00113Q0020E600100003000F2Q002201116Q00E5000F0011000200268E000F00820001000B0004D83Q008200012Q00FC000F00013Q0006EA000400830001000F0004D83Q008300012Q00FC00045Q0004D83Q008500010004D83Q003C000100263A0002008A000100230004D83Q008A000100268E0004008A000100240004D83Q008A0001001206000200233Q0012060001000A3Q00268E0001008E0001000A0004D83Q008E00012Q0018010200023Q00268E000100020001000B0004D83Q00020001001255000600254Q00E3000700014Q00A60006000200080004D83Q009E0001001255000B00263Q00208F000B000B00274Q000C00096Q000D8Q000B000D000200062Q000B009E00013Q0004D83Q009E0001000640000A009E000100020004D83Q009E00012Q00220102000A3Q00069C00060094000100020004D83Q009400012Q0074000300033Q001206000100023Q0004D83Q000200012Q00CF3Q00017Q00213Q0003183Q004C6567656E6461727953652Q74696E6773436C612Q73696303083Q0053652Q74696E677303163Q0059852A7242992B6744A4307B49BC367E448E327E439F03043Q001730EB5E03023Q005F4703143Q00496E74652Q727570744C4672616D654361636865030B3Q00696E697469616C697A6564028Q00026Q000840030D3Q0052656769737465724576656E7403183Q0049F4F1696800E259F6F47E7600E643E9ED7E7416F758FFFC03073Q00B21CBAB83D375303203Q00F1E36E08CD3DC52QE16B1FD33DC1FBE36808CD27DBF0E8750EC73EC1EDEF6B1903073Q0095A4AD275C926E026Q001040026Q00F03F031D3Q00C609392B2528C3023C33393AC0132F3C323ADD093533252EC303312B3F03063Q007B9347707F7A03143Q00F9E3AB4579FFFDA75D6AEFECB14579FFF9A3437203053Q0026ACADE211027Q004003093Q0053657453637269707403073Q00621F09F9481F3803043Q008F2D714C2Q01031C3Q00D88BAE4F2F806319C189A45A23876C1FC584A955359F6C0FD984B54F03083Q005C8DC5E71B70D333031B3Q00D3D1A397EED5CFAF8FFDC5DEB997EEC5D7AB8DFFC3D3B590E5C9CF03053Q00B1869FEAC303133Q0088C51694F68EDB1A8CE59ECA0C94F68EDF109003053Q00A9DD8B5FC0031A3Q00EBA5560B1D15EEAE53130107EDBF40160C12FBB94D0A2Q12FBAF03063Q0046BEEB1F5F42006D3Q0012B53Q00013Q00206Q00024Q00015Q00122Q000200033Q00122Q000300046Q0001000300028Q00019Q0000122Q000100053Q00202Q00010001000600202Q00010001000700062Q0001006C000100010004D83Q006C0001001206000100083Q00268E00010021000100090004D83Q00210001001255000200053Q00200601020002000600202Q00020002000A4Q00045Q00122Q0005000B3Q00122Q0006000C6Q000400066Q00023Q000100122Q000200053Q00202Q00020002000600202Q00020002000A4Q00045Q00122Q0005000D3Q00122Q0006000E6Q000400066Q00023Q000100122Q0001000F3Q00268E00010034000100100004D83Q00340001001255000200053Q00200601020002000600202Q00020002000A4Q00045Q00122Q000500113Q00122Q000600126Q000400066Q00023Q000100122Q000200053Q00202Q00020002000600202Q00020002000A4Q00045Q00122Q000500133Q00122Q000600146Q000400066Q00023Q000100122Q000100153Q000E2C000F0045000100010004D83Q00450001001255000200053Q00201800020002000600202Q0002000200164Q00045Q00122Q000500173Q00122Q000600186Q0004000600020006D700053Q000100022Q00E38Q0022017Q004A00020005000100122Q000200053Q00202Q00020002000600302Q00020007001900044Q006C000100268E00010058000100080004D83Q00580001001255000200053Q00200601020002000600202Q00020002000A4Q00045Q00122Q0005001A3Q00122Q0006001B6Q000400066Q00023Q000100122Q000200053Q00202Q00020002000600202Q00020002000A4Q00045Q00122Q0005001C3Q00122Q0006001D6Q000400066Q00023Q000100122Q000100103Q00268E0001000E000100150004D83Q000E0001001255000200053Q00200601020002000600202Q00020002000A4Q00045Q00122Q0005001E3Q00122Q0006001F6Q000400066Q00023Q000100122Q000200053Q00202Q00020002000600202Q00020002000A4Q00045Q00122Q000500203Q00122Q000600216Q000400066Q00023Q000100122Q000100093Q0004D83Q000E00012Q00CF3Q00013Q00013Q00333Q00031B3Q008D963508878B2C192Q943F1D8B8C231F909932129D94230F8C972C03043Q005C2QD87C03133Q006E1C8574C26802896CD178139F74C26806837003053Q009D3B52CC20031A3Q000D10CACED6D9E3941412C0DBDADEEC98160AC6C8DBDFE3851D1A03083Q00D1585E839A898AB303183Q001D8FED4821100107048DE75D2D170E111D82E7593B07140603083Q004248C1A41C7E435103023Q005F4703143Q00496E74652Q727570744C556E69747343616368650003063Q00737472696E6703053Q006D6174636803093Q00E92DA55D367AE638AD03063Q0016874CC83846028Q00031C3Q00B81ED11062D2BD15D4087EC0BE04C70775C0A31EDD0862D2B911CA1003063Q0081ED5098443D031D3Q0064862DC7232468748428D03D246C6E8B2CD232392Q7D9731C338366C7403073Q003831C864937C7703073Q00EF169EDEE21B9303043Q0090AC5EDF03143Q0011218B731B3C926208238166173B9D74102E907303043Q0027446FC203043Q00F587D4F303063Q00D7B6C687A719026Q00F03F030C3Q004B69636B5370652Q6C49647303073Q00AE61CB66A36CC603043Q0028ED298A030F3Q00556E69744368612Q6E656C496E666F0100030C3Q00556E69745265616374696F6E03063Q00D778FBE14FD503053Q002AA7149A9803063Q005AF2A35B743303063Q00412A9EC22211026Q00104003043Q003906613803083Q008E7A47326C4D8D7B030F3Q00556E697443617374696E67496E666F03063Q0005AEFE013E0703053Q005B75C29F7803063Q000A113F0130E303073Q00447A7D5E78559103073Q00040CCA52C4F0BE03073Q00DA777CAF3EA8B903063Q00B1F15AC3A0E403043Q00A4C59028030D3Q008AFEBE8ECFA496E0BEBFC4A68603063Q00D6E390CAEBBD06D34Q003C00075Q00122Q000800013Q00122Q000900026Q00070009000200062Q00010018000100070004D83Q001800012Q00E300075Q001206000800033Q001206000900044Q00E500070009000200069B00010018000100070004D83Q001800012Q00E300075Q001206000800053Q001206000900064Q00E500070009000200069B00010018000100070004D83Q001800012Q00E300075Q001206000800073Q001206000900084Q00E50007000900020006390001001C000100070004D83Q001C0001001255000700093Q0020E600070007000A0020A000070002000B0004D83Q00D200010012550007000C3Q00201901070007000D4Q000800026Q00095Q00122Q000A000E3Q00122Q000B000F6Q0009000B6Q00073Q000200062Q000700D200013Q0004D83Q00D20001001206000700104Q0074000800093Q00268E00070049000100100004D83Q004900012Q0074000800084Q003C000A5Q00122Q000B00113Q00122Q000C00126Q000A000C000200062Q000100370001000A0004D83Q003700012Q00E3000A5Q001206000B00133Q001206000C00144Q00E5000A000C00020006390001003D0001000A0004D83Q003D00012Q00E3000A5Q00122Q010B00153Q00122Q000C00166Q000A000C00024Q0008000A3Q00044Q004800012Q00E3000A5Q001206000B00173Q001206000C00184Q00E5000A000C0002000639000100480001000A0004D83Q004800012Q00E3000A5Q001206000B00193Q001206000C001A4Q00E5000A000C00022Q00220108000A3Q0012060007001B3Q00268E000700280001001B0004D83Q00280001001255000A00093Q0020E6000A000A001C2Q000D010A000A00040006EA000900510001000A0004D83Q005100012Q00E3000900013Q000689000900D200013Q0004D83Q00D20001001206000A00104Q0074000B000B3Q000E2C001000B70001000A0004D83Q00B700012Q00FC000B6Q0053000C5Q00122Q000D001D3Q00122Q000E001E6Q000C000E000200062Q000800880001000C0004D83Q00880001001206000C00104Q0074000D00163Q00268E000C0060000100100004D83Q006000010012550017001F4Q00A4001800026Q0017000200204Q001600206Q0015001F6Q0014001E6Q0013001D6Q0012001C6Q0011001B6Q0010001A6Q000F00196Q000E00186Q000D00173Q00262Q00130083000100200004D83Q00830001001255001700214Q005A00185Q00122Q001900223Q00122Q001A00236Q0018001A00024Q001900026Q00170019000200062Q000B0085000100170004D83Q00850001001255001700214Q004400185Q00122Q001900243Q00122Q001A00256Q0018001A00024Q001900026Q00170019000200262Q00170084000100260004D83Q008400012Q00D6000B6Q00FC000B00013Q0004D83Q00B600010004D83Q006000010004D83Q00B600012Q00E3000C5Q001206000D00273Q001206000E00284Q00E5000C000E0002000639000800B60001000C0004D83Q00B60001001206000C00104Q0074000D00153Q00268E000C0090000100100004D83Q00900001001255001600294Q007F001700026Q00160002001E4Q0015001E6Q0014001D6Q0013001C6Q0012001B6Q0011001A6Q001000196Q000F00186Q000E00176Q000D00163Q00262Q001400B2000100200004D83Q00B20001001255001600214Q005A00175Q00122Q0018002A3Q00122Q0019002B6Q0017001900024Q001800026Q00160018000200062Q000B00B4000100160004D83Q00B40001001255001600214Q004400175Q00122Q0018002C3Q00122Q0019002D6Q0017001900024Q001800026Q00160018000200262Q001600B3000100260004D83Q00B300012Q00D6000B6Q00FC000B00013Q0004D83Q00B600010004D83Q00900001001206000A001B3Q00268E000A00550001001B0004D83Q00550001000689000B00D200013Q0004D83Q00D20001001255000C00093Q00200F010C000C000A4Q000D3Q00034Q000E5Q00122Q000F002E3Q00122Q0010002F6Q000E001000024Q000D000E00044Q000E5Q00122Q000F00303Q00122Q001000316Q000E001000024Q000D000E00024Q000E5Q00122Q000F00323Q00122Q001000336Q000E001000024Q000D000E00084Q000C0002000D00044Q00D200010004D83Q005500010004D83Q00D200010004D83Q002800012Q00CF3Q00017Q00743Q0003083Q00435F412Q644F6E73030D3Q004973412Q644F6E4C6F61646564030C3Q008FB2DBD395B82QDDB3BEC6D203043Q00BCC7D7A9030C3Q004865726F526F746174696F6E03073Q004865726F4C696203043Q00556E697403063Q00506C6179657203163Q00476574456E656D696573496E4D656C2Q6552616E6765026Q00244003113Q00476574456E656D696573496E52616E6765026Q00444003063Q0054617267657403173Q00476574456E656D696573496E53706C61736852616E6765028Q0003063Q00487244617461030D3Q00546172676574496E4D656C2Q65030D3Q00546172676574496E52616E6765030E3Q00546172676574496E53706C617368030D3Q004C65667449636F6E4672616D6503093Q00497356697369626C65030C3Q004379636C655370652Q6C494403023Q00494403053Q00546F6B656E026Q00F03F030B3Q00435F4E616D65506C61746503133Q004765744E616D65506C617465466F72556E697403113Q006E616D65506C617465556E69744755494403083Q00556E69744755494403093Q00F1064A68EDF31F5A6903053Q00889C693F1B03073Q004379636C654D4F2Q0103093Q004379636C65556E69740100030D3Q004D61696E49636F6E4672616D6503073Q0054657874757265030E3Q00476574566572746578436F6C6F72029A5Q99D93F030A3Q004E6F74496E52616E676503073Q005370652Q6C494403023Q005F47030D3Q004C48656B696C6952656349644C030D3Q004C4D617844505352656349644C03103Q004765745370652Q6C432Q6F6C646F776E025Q00EFED4003183Q004C6567656E6461727953652Q74696E6773436C612Q73696303083Q0053652Q74696E677303103Q0010C027AA8432C527B38D30DC2BA28D1103053Q00E863B042C6026Q00794003043Q006D61746803063Q0072616E646F6D026Q0059C0026Q005940030B3Q004765744E65745374617473030F3Q00556E697443617374696E67496E666F03063Q00FC2D291F7E9F03083Q004C8C4148661BED99030F3Q00556E69744368612Q6E656C496E666F03063Q005AD617CBD21303073Q00DE2ABA76B2B76103063Q0075E94F8351E503043Q00EA3D8C2403083Q0048656B696C69444203083Q0070726F66696C657303073Q0044656661756C7403073Q00746F2Q676C657303043Q006D6F646503053Q0076616C7565034Q0003083Q0033D8BB711B28CBBF03053Q006F41BDDA1203043Q00475E1A3903073Q00CF232B7B556B3C025Q0097F34003073Q005072696D6172792Q033Q00414F4503063Q00982FAC59B48603053Q00E4D54ED41D027Q0040030A3Q00476C6F62616C44617461030E3Q00526F746174696F6E48656C706572030E3Q009543A204FF8E43B82DEE8B5CB31703053Q008BE72CD66503063Q00F1EA0D571CB803083Q0076B98F663E70D151030E3Q00456E656D696573496E4D656C2Q652Q033Q006D6178030C3Q004C52616E6765436865636B4C030C3Q00556E697473496E4D656C2Q6503063Q0048656B696C6903053Q005374617465030E3Q006163746976655F656E656D696573030E3Q00456E656D696573496E52616E6765030C3Q00556E697473496E52616E6765030E3Q00432Q6F6C646F776E546F2Q676C6503063Q00746F2Q676C6503093Q00632Q6F6C646F776E73030C3Q00466967687452656D61696E73030B3Q006C6F6E676573745F2Q746403053Q004379636C6503143Q0048656B696C69446973706C61795072696D617279030F3Q005265636F2Q6D656E646174696F6E7303093Q00696E64696361746F720003053Q005F692AEAA003083Q00583C104986C5757C03063Q007DEBE0EC716303053Q0021308A98A803063Q004D6178447073030C3Q0047657454696D65546F44696503083Q00536D617274416F65030D3Q0052616E6765546F54617267657403063Q0066172256C42303063Q005712765031A1029B023Q006D00028Q0002000200014Q00028Q00028Q000300013Q00062Q0003009A020100020004D83Q009A02012Q00E3000200024Q003B0002000100014Q000200036Q0002000100014Q000200046Q0002000100014Q000200056Q00020001000100122Q000200013Q00202Q0002000200024Q000300063Q00122Q000400033Q00122Q000500046Q000300056Q00023Q000300062Q000200FE00013Q0004D83Q00FE0001000689000300FE00013Q0004D83Q00FE0001001255000400053Q0012C2000500063Q00202Q00060005000700202Q00060006000800202Q00060006000900122Q0008000A6Q00060008000200202Q00070005000700202Q00070007000800202Q00070007000B00122Q0009000C6Q00070009000200202Q00080005000700202Q00080008000D00202Q00080008000E00122Q000A000A6Q0008000A00024Q000900063Q000E2Q000F0032000100090004D83Q003200012Q00E3000900073Q0020E60009000900102Q008C000A00063Q00102600090011000A2Q008C000900073Q000EDE000F0039000100090004D83Q003900012Q00E3000900073Q0020E60009000900102Q008C000A00073Q00102600090012000A2Q008C000900083Q000EDE000F0040000100090004D83Q004000012Q00E3000900073Q0020E60009000900102Q008C000A00083Q00102600090013000A0020E6000900040014000689000900AA00013Q0004D83Q00AA00010020E60009000400140020F20009000900152Q00F4000900020002000689000900AA00013Q0004D83Q00AA00010012060009000F4Q0074000A000A3Q00268E000900550001000F0004D83Q005500012Q00E3000B00073Q002005010B000B001000202Q000C0004001400202Q000C000C001700102Q000B0016000C4Q000B00073Q00202Q000B000B001000202Q000A000B001800122Q000900193Q00268E0009004A000100190004D83Q004A0001000689000A009C00013Q0004D83Q009C0001001206000B000F4Q0074000C000C3Q00268E000B005B0001000F0004D83Q005B0001001255000D001A3Q002077000D000D001B4Q000E000A6Q000D000200024Q000C000D3Q00062Q000C008E00013Q0004D83Q008E00010020E6000D000C001C000689000D008E00013Q0004D83Q008E0001001206000D000F4Q0074000E000E3Q00268E000D00690001000F0004D83Q006900010020E6000E000C001C0012FE000F001D6Q001000063Q00122Q0011001E3Q00122Q0012001F6Q001000126Q000F3Q000200062Q000F00800001000E0004D83Q00800001001206000F000F3Q00268E000F00750001000F0004D83Q007500012Q00E3001000073Q00208700100010001000302Q0010002000214Q001000073Q00202Q00100010001000302Q00100022002300044Q00BB00010004D83Q007500010004D83Q00BB0001001206000F000F3Q00268E000F00810001000F0004D83Q008100012Q00E3001000073Q00208700100010001000302Q0010002000234Q001000073Q00202Q00100010001000302Q00100022002100044Q00BB00010004D83Q008100010004D83Q00BB00010004D83Q006900010004D83Q00BB0001001206000D000F3Q00268E000D008F0001000F0004D83Q008F00012Q00E3000E00073Q002087000E000E001000302Q000E002000234Q000E00073Q00202Q000E000E001000302Q000E0022002300044Q00BB00010004D83Q008F00010004D83Q00BB00010004D83Q005B00010004D83Q00BB0001001206000B000F3Q000E2C000F009D0001000B0004D83Q009D00012Q00E3000C00073Q002087000C000C001000302Q000C002000234Q000C00073Q00202Q000C000C001000302Q000C0022002300044Q00BB00010004D83Q009D00010004D83Q00BB00010004D83Q004A00010004D83Q00BB00010012060009000F3Q00268E000900B40001000F0004D83Q00B400012Q00E3000A00073Q0020AD000A000A001000302Q000A0016000F4Q000A00073Q00202Q000A000A001000302Q000A0020002300122Q000900193Q00268E000900AB000100190004D83Q00AB00012Q00E3000A00073Q0020E6000A000A0010003050000A002200230004D83Q00BB00010004D83Q00AB00010020E6000900040024000689000900F300013Q0004D83Q00F300010020E60009000400240020F20009000900152Q00F4000900020002000689000900F300013Q0004D83Q00F300010012060009000F4Q0074000A000C3Q00268E000900DC0001000F0004D83Q00DC00010020E6000D0004002400200A000D000D002500202Q000D000D00264Q000D0002000F4Q000C000F6Q000B000E6Q000A000D3Q00262Q000B00D8000100190004D83Q00D80001000EDE002700D80001000B0004D83Q00D8000100263A000C00D8000100190004D83Q00D800012Q00E3000D00073Q0020E6000D000D0010003050000D002800210004D83Q00DB00012Q00E3000D00073Q0020E6000D000D0010003050000D00280023001206000900193Q00268E000900C5000100190004D83Q00C500010020E6000D000400240020E6000D000D0017000689000D00ED00013Q0004D83Q00ED00012Q00E3000D00073Q0020E6000D000D00100020E6000D000D00280006F6000D00ED000100010004D83Q00ED00012Q00E3000D00073Q002025000D000D001000202Q000E0004002400202Q000E000E001700102Q000D0029000E00044Q00FE00012Q00E3000D00073Q0020E6000D000D0010003050000D0029000F0004D83Q00FE00010004D83Q00C500010004D83Q00FE00010012060009000F3Q00268E000900F40001000F0004D83Q00F400012Q00E3000A00073Q002087000A000A001000302Q000A0029000F4Q000A00073Q00202Q000A000A001000302Q000A0028002300044Q00FE00010004D83Q00F400010012550004002A3Q0012550005002A3Q0020E600050005002B0006F6000500042Q0100010004D83Q00042Q012Q000301055Q0010260004002B00050012550004002A3Q0012550005002A3Q0020E600050005002C0006F60005000B2Q0100010004D83Q000B2Q012Q000301055Q0010260004002C00050002B800045Q0002B8000500013Q0006D700060002000100012Q00E33Q00063Q0006D700070003000100012Q00E33Q00063Q0012590008002D3Q00122Q0009002E6Q00080002000900122Q000A002F3Q00202Q000A000A00304Q000B00063Q00122Q000C00313Q00122Q000D00326Q000B000D00024Q000A000A000B00062Q000A001F2Q0100010004D83Q001F2Q01001206000A00333Q001255000B00343Q002031000B000B003500122Q000C00363Q00122Q000D00376Q000B000D00024Q000A000A000B00122Q000B00386Q000B0001000E4Q000F000E000A00122Q001000396Q001100063Q00122Q0012003A3Q00122Q0013003B6Q001100136Q00103Q001800122Q0019003C6Q001A00063Q00122Q001B003D3Q00122Q001C003E6Q001A001C6Q00193Q002000122Q002100013Q00202Q0021002100024Q002200063Q00122Q0023003F3Q00122Q002400406Q002200246Q00213Q002200062Q0021007E2Q013Q0004D83Q007E2Q010006890022007E2Q013Q0004D83Q007E2Q01001255002300413Q0006890023004A2Q013Q0004D83Q004A2Q01001255002300413Q00204200230023004200202Q00230023004300202Q00230023004400202Q00230023004500202Q00230023004600062Q0023004B2Q0100010004D83Q004B2Q01001206002300474Q00FC00246Q003C002500063Q00122Q002600483Q00122Q002700496Q00250027000200062Q002300582Q0100250004D83Q00582Q012Q00E3002500063Q0012060026004A3Q0012060027004B4Q00E5002500270002000639002300592Q0100250004D83Q00592Q012Q00FC002400014Q000301253Q00010030500025004C00210006D700260004000100012Q0022012Q00253Q0006D7002700050001000B2Q00E33Q00064Q0022012Q00244Q0022012Q00064Q0022012Q00264Q0022012Q00074Q0022012Q00094Q0022012Q000F4Q0022012Q00044Q0022012Q00144Q0022012Q00054Q0022012Q001D4Q008A002800276Q00280001000200202Q00290028004D00202Q002A0028004E00122Q002B002A3Q00202Q002B002B002B00062Q002B007C2Q013Q0004D83Q007C2Q01001206002B000F3Q00268E002B00722Q01000F0004D83Q00722Q01001255002C002A3Q002027002C002C002B00102Q002C004D002900122Q002C002A3Q00202Q002C002C002B00102Q002C004E002A00044Q007C2Q010004D83Q00722Q012Q00C700235Q0004D83Q008D2Q010012550023002A3Q0020E600230023002B0006890023008D2Q013Q0004D83Q008D2Q010012060023000F3Q00268E002300832Q01000F0004D83Q00832Q010012550024002A3Q00207D00240024002B00302Q0024004D000F00122Q0024002A3Q00202Q00240024002B00302Q0024004E000F00044Q008D2Q010004D83Q00832Q010006D700230006000100092Q0022012Q00064Q0022012Q00074Q0022012Q00094Q0022012Q000F4Q00E33Q00064Q0022012Q00044Q0022012Q00144Q0022012Q00054Q0022012Q001D3Q0012C8002400013Q00202Q0024002400024Q002500063Q00122Q0026004F3Q00122Q002700506Q002500276Q00243Q002500062Q002400BC2Q013Q0004D83Q00BC2Q01000689002500BC2Q013Q0004D83Q00BC2Q010012060026000F4Q0074002700293Q000E2C000F00AA2Q0100260004D83Q00AA2Q012Q0074002700273Q0006D700270007000100012Q0022012Q00233Q001206002600193Q00268E002600B42Q0100510004D83Q00B42Q01001255002A002A3Q0020E6002A002A002C000689002A00BC2Q013Q0004D83Q00BC2Q01001255002A002A3Q0020E6002A002A002C001026002A002900290004D83Q00BC2Q0100268E002600A42Q0100190004D83Q00A42Q012Q0022012A00274Q0010002A000100024Q0028002A6Q002900283Q00122Q002600513Q00044Q00A42Q012Q00E3002600073Q00202F00260026005200122Q0027002F3Q00202Q0027002700304Q002800063Q00122Q002900543Q00122Q002A00556Q0028002A00024Q00270027002800062Q002700C82Q0100010004D83Q00C82Q01001206002700473Q0010260026005300270006890021002502013Q0004D83Q002502010006890022002502013Q0004D83Q002502012Q00E3002600073Q00205800260026005200202Q0026002600534Q002700063Q00122Q002800563Q00122Q002900576Q00270029000200062Q00260025020100270004D83Q002502010012060026000F3Q000E2C005100F22Q0100260004D83Q00F22Q012Q00E3002700073Q0020BE00270027005200122Q002800343Q00202Q00280028005900122Q0029002A3Q00202Q00290029005A00202Q00290029005B00122Q002A005C3Q00202Q002A002A005D00202Q002A002A005E4Q0028002A000200102Q0027005800284Q002700073Q00202Q00270027005200122Q002800343Q00202Q00280028005900122Q0029002A3Q00202Q00290029005A00202Q00290029006000122Q002A005C3Q00202Q002A002A005D00202Q002A002A005E4Q0028002A000200102Q0027005F002800044Q008E020100268E00260005020100190004D83Q000502012Q00E3002700073Q00202B00270027005200122Q0028005C3Q00202Q00280028005D00202Q00280028006200202Q00280028006300102Q0027006100284Q002700073Q00202Q00270027005200122Q0028005C3Q00202Q00280028005D00202Q00280028006500062Q00280003020100010004D83Q000302010012060028000F3Q001026002700640028001206002600513Q00268E002600D72Q01000F0004D83Q00D72Q012Q00E3002700073Q0020B100270027005200122Q0028002A3Q00202Q00280028002B00202Q00280028004D00102Q0027002900284Q002700073Q00202Q00270027005200122Q002800673Q00202Q00280028006800202Q00280028001900202Q00280028006900262Q0028001F0201006A0004D83Q001F0201001255002800673Q0020BA00280028006800202Q00280028001900202Q0028002800694Q002900063Q00122Q002A006B3Q00122Q002B006C6Q0029002B000200062Q00280020020100290004D83Q002002012Q00D600286Q00FC002800013Q001026002700660028001206002600193Q0004D83Q00D72Q010004D83Q008E02010006890024006B02013Q0004D83Q006B02010006890025006B02013Q0004D83Q006B02012Q00E3002600073Q00205800260026005200202Q0026002600534Q002700063Q00122Q0028006D3Q00122Q0029006E6Q00270029000200062Q0026006B020100270004D83Q006B02010012060026000F3Q000E2C00190042020100260004D83Q004202012Q00E3002700073Q00201E01270027005200302Q0027006100214Q002700073Q00202Q00270027005200122Q0028006F3Q00202Q0028002800704Q00280001000200062Q00280040020100010004D83Q004002010012060028000F3Q001026002700640028001206002600513Q00268E0026004E0201000F0004D83Q004E02012Q00E3002700073Q00203300270027005200122Q0028002A3Q00202Q00280028002C00202Q00280028002900102Q0027002900284Q002700073Q00202Q00270027005200302Q00270066002300122Q002600193Q00268E00260033020100510004D83Q003302012Q00E3002700073Q00206E00270027005200122Q002800343Q00202Q00280028005900122Q0029002A3Q00202Q00290029005A00202Q00290029005B00122Q002A006F3Q00202Q002A002A00714Q002A002B6Q00283Q000200102Q0027005800284Q002700073Q00202Q00270027005200122Q002800343Q00202Q00280028005900122Q0029002A3Q00202Q00290029005A00202Q00290029006000122Q002A006F3Q00202Q002A002A00714Q002A002B6Q00283Q000200102Q0027005F002800044Q008E02010004D83Q003302010004D83Q008E02010012060026000F3Q00268E002600750201000F0004D83Q007502012Q00E3002700073Q0020AD00270027005200302Q00270029000F4Q002700073Q00202Q00270027005200302Q00270066002300122Q002600193Q000E2C00510084020100260004D83Q008402012Q00E3002700073Q00204600270027005200122Q0028002A3Q00202Q00280028005A00202Q00280028005B00102Q0027005800284Q002700073Q00202Q00270027005200122Q0028002A3Q00202Q00280028005A00202Q00280028006000102Q0027005F002800044Q008E020100268E0026006C020100190004D83Q006C02012Q00E3002700073Q0020D500270027005200302Q0027006100234Q002700073Q00202Q00270027005200302Q00270064000F00122Q002600513Q00044Q006C02012Q00E3002600073Q0020780026002600524Q002700086Q002800063Q00122Q002900733Q00122Q002A00746Q0028002A6Q00273Q000200102Q00260072002700122Q0026000F6Q00268Q00026Q00CF3Q00013Q00083Q00033Q00028Q0003073Q0047657454696D65025Q00408F40010E3Q001206000100013Q00268E00010001000100010004D83Q000100010006893Q000A00013Q0004D83Q000A0001001255000200024Q001A0102000100020020FF0002000200032Q007E00023Q00022Q0018010200024Q0074000200024Q0018010200023Q0004D83Q000100012Q00CF3Q00017Q00033Q00028Q0003073Q0047657454696D65025Q00408F40010E3Q001206000100013Q00268E00010001000100010004D83Q000100010006893Q000A00013Q0004D83Q000A0001001255000200024Q001A0102000100020020FF0002000200032Q007E00023Q00022Q0018010200024Q0074000200024Q0018010200023Q0004D83Q000100012Q00CF3Q00017Q000A3Q00028Q00026Q00F03F03103Q004765745370652Q6C432Q6F6C646F776E03043Q007479706503063Q00159974361E9E03043Q00547BEC1903063Q00FE9EA715A9A703063Q00D590EBCA77CC03073Q0047657454696D65025Q00408F40012C3Q001206000100014Q0074000200033Q000E2C00020006000100010004D83Q00060001001206000400014Q0018010400023Q00268E00010002000100010004D83Q00020001001255000400034Q008400058Q0004000200054Q000300056Q000200043Q00122Q000400046Q000500026Q0004000200024Q00055Q00122Q000600053Q00122Q000700066Q00050007000200062Q00040029000100050004D83Q00290001001255000400044Q0090000500036Q0004000200024Q00055Q00122Q000600073Q00122Q000700086Q00050007000200062Q00040029000100050004D83Q00290001000EDE00010029000100020004D83Q00290001000EDE00010029000100030004D83Q00290001001255000400094Q00F10004000100024Q0004000400024Q00040003000400202Q00040004000A4Q000400023Q001206000100023Q0004D83Q000200012Q00CF3Q00017Q00113Q00028Q00030D3Q004E554D5F4241475F534C4F5453026Q00F03F030B3Q00435F436F6E7461696E657203143Q00476574436F6E7461696E65724E756D536C6F747303143Q00476574436F6E7461696E65724974656D4C696E6B03063Q00435F4974656D030B3Q004765744974656D496E666F030C3Q004765744974656D436F756E74030F3Q004765744974656D432Q6F6C646F776E03043Q007479706503063Q002D0DD3282D3103073Q002D4378BE4A484303063Q002E37E0A7FC9A03083Q008940428DC599E88E03073Q0047657454696D65025Q00408F4001703Q001206000100013Q00268E00010001000100010004D83Q00010001001206000200013Q001255000300023Q001206000400033Q0004BD0002006C0001001206000600033Q00125F000700043Q00202Q0007000700054Q000800056Q00070002000200122Q000800033Q00042Q0006006B0001001206000A00014Q0074000B000B3Q00268E000A0010000100010004D83Q00100001001255000C00043Q002083000C000C00064Q000D00056Q000E00096Q000C000E00024Q000B000C3Q00062Q000B006A00013Q0004D83Q006A0001001206000C00014Q0074000D000F3Q00268E000C001C000100010004D83Q001C0001001255001000073Q0020F80010001000084Q0011000B6Q00100002001B4Q000F001B6Q000E001A6Q000E00196Q000E00186Q000E00176Q000E00166Q000E00156Q000E00146Q000E00136Q000E00126Q000E00116Q000D00103Q00062Q000D006A00013Q0004D83Q006A0001000689000F006A00013Q0004D83Q006A00010006393Q006A0001000F0004D83Q006A0001001255001000073Q0020E60010001000092Q00220111000F4Q00F4001000020002000EDE0001006A000100100004D83Q006A0001001206001000014Q0074001100123Q00268E00100040000100030004D83Q00400001001206001300014Q0018011300023Q00268E0010003C000100010004D83Q003C0001001255001300043Q0020EE00130013000A4Q0014000F6Q0013000200144Q001200146Q001100133Q00122Q0013000B6Q001400116Q0013000200024Q00145Q00122Q0015000C3Q00122Q0016000D6Q00140016000200062Q00130064000100140004D83Q006400010012550013000B4Q0090001400126Q0013000200024Q00145Q00122Q0015000E3Q00122Q0016000F6Q00140016000200062Q00130064000100140004D83Q00640001000EDE00010064000100110004D83Q00640001000EDE00010064000100120004D83Q00640001001255001300104Q00F10013000100024Q0013001300114Q00130012001300202Q0013001300114Q001300023Q001206001000033Q0004D83Q003C00010004D83Q006A00010004D83Q001C00010004D83Q006A00010004D83Q0010000100043E0006000E000100043E0002000700012Q0074000200024Q0018010200023Q0004D83Q000100012Q00CF3Q00017Q00023Q00028Q0003053Q00706169727301113Q001206000100013Q00268E00010001000100010004D83Q00010001001255000200024Q00E300036Q00A60002000200040004D83Q000B00010006390005000B00013Q0004D83Q000B00012Q00FC00076Q0018010700023Q00069C00020007000100020004D83Q000700012Q00FC000200014Q0018010200023Q0004D83Q000100012Q00CF3Q00017Q00133Q0003073Q0040B8A9E77862B303053Q001910CAC08A03063Q0048656B696C69030B3Q00446973706C6179502Q6F6C03073Q005072696D617279030F3Q005265636F2Q6D656E646174696F6E732Q033Q00DCE48803063Q00949DABCD82C92Q033Q00414F4503073Q0013C67D24D0E43A03063Q009643B41449B103083Q006E756D49636F6E73028Q002Q033Q00AC373F03043Q002DED787A03073Q00E7FAAB21D6FABB03043Q004CB788C22Q033Q005BC9C003073Q00741A868558302F00674Q005C5Q00024Q00015Q00122Q000200013Q00122Q000300026Q00010003000200122Q000200033Q00062Q0002000E00013Q0004D83Q000E0001001255000200033Q0020E60002000200040020E60002000200050020E60002000200060006F60002000F000100010004D83Q000F00012Q000301026Q00C13Q000100022Q00112Q015Q00122Q000200073Q00122Q000300086Q00010003000200122Q000200033Q00062Q0002002000013Q0004D83Q002000012Q00E3000200013Q0006890002002000013Q0004D83Q00200001001255000200033Q0020E60002000200040020E60002000200090020E60002000200060006F600020021000100010004D83Q002100012Q000301026Q00C13Q000100022Q005C00013Q00024Q00025Q00122Q0003000A3Q00122Q0004000B6Q00020004000200122Q000300033Q00062Q0003003000013Q0004D83Q00300001001255000300033Q0020E60003000300040020E60003000300050020E600030003000C0006F600030031000100010004D83Q003100010012060003000D4Q00C10001000200032Q001101025Q00122Q0003000E3Q00122Q0004000F6Q00020004000200122Q000300033Q00062Q0003004200013Q0004D83Q004200012Q00E3000300013Q0006890003004200013Q0004D83Q00420001001255000300033Q0020E60003000300040020E60003000300090020E600030003000C0006F600030043000100010004D83Q004300010012060003000D4Q00C10001000200032Q003700023Q00024Q00035Q00122Q000400103Q00122Q000500116Q00030005000200202Q00020003000D4Q00035Q00122Q000400123Q00122Q000500136Q00030005000200202Q00020003000D0006D700033Q0001000A2Q00E38Q00E33Q00024Q00E33Q00034Q00E33Q00044Q00E33Q00054Q00E33Q00064Q00E33Q00074Q00E33Q00084Q00E33Q00094Q00E33Q000A4Q001B010400033Q00202Q00053Q00054Q00040002000200102Q0002000500044Q000400013Q00062Q0004006500013Q0004D83Q006500012Q0022010400033Q0020E600053Q00092Q00F40004000200020010260002000900042Q0018010200024Q00CF3Q00013Q00013Q00433Q00028Q00026Q00F03F03083Q00616374696F6E494403043Q0077616974025Q00408F4003093Q00696E64696361746F7203053Q001DD8A3E8B803063Q00127EA1C084DD03063Q0048656B696C6903053Q00537461746503083Q0073652Q74696E677303043Q007370656303053Q006379636C652Q0103183Q004C6567656E6461727953652Q74696E6773436C612Q73696303083Q0053652Q74696E677303093Q005E3DBA0B75462BA20103053Q00363F48CE64030E3Q004973506C617965724D6F76696E67023Q00402244634103053Q00436C612Q7303093Q006162696C697469657303043Q006974656D03143Q00476574496E76656E746F72794974656D4C696E6B03063Q00D8554463E06903063Q001BA839251A85026Q002A4003063Q003DA67DB1D23F03053Q00B74DCA1CC8026Q002C4003063Q00073F8811122103043Q00687753E9026Q00304003063Q00E5F4263B46E703053Q002395984742026Q003140027Q004003063Q00435F4974656D03123Q004765744974656D496E666F496E7374616E74026Q00084003063Q0009E443A93F0B03053Q005A798822D0026Q002E4003063Q00D7025407C21C03043Q007EA76E35026Q002440026Q001040026Q001840026Q001C4003023Q00444203073Q0070726F66696C6503073Q00746F2Q676C657303073Q00706F74696F6E7303053Q0076616C7565030D3Q0019201DC8D32B341F20D6DD323803063Q005F5D704E98BC030F3Q00F5F08805E1ACD7C52QB51AF0B7DDCF03073Q00B2A195E57584DE030C3Q004765744974656D436F756E7403043Q006D6174682Q033Q00616273026Q00144003063Q0073656C656374030B3Q004765744974656D496E666F03073Q00435F5370652Q6C030D3Q0049735370652Q6C557361626C65000156012Q001206000100014Q0074000200023Q000E2C0002004C2Q0100010004D83Q004C2Q01000689000200552Q013Q0004D83Q00552Q010020E6000300020003000689000300552Q013Q0004D83Q00552Q010020E600030002000300206900040002000400202Q00040004000500202Q0005000200064Q00065Q00122Q000700073Q00122Q000800086Q00060008000200062Q00050023000100060004D83Q00230001001255000500093Q00208800050005000A00202Q00050005000B00202Q00050005000C00202Q00050005000D00262Q000500230001000E0004D83Q002300010012550005000F3Q0020050005000500104Q00065Q00122Q000700113Q00122Q000800126Q0006000800024Q00050005000600262Q000500240001000E0004D83Q002400012Q00D600056Q00FC000500013Q00124C000600136Q0006000100024Q000700016Q000800036Q00070002000200062Q0005003400013Q0004D83Q003400012Q00E3000800024Q0022010900034Q00F40008000200020006890008003400013Q0004D83Q00340001001206000800144Q0018010800023Q0004D83Q00492Q0100263A000300252Q0100010004D83Q00252Q01001255000800093Q0020E60008000800150020E60008000800162Q000D010800080003000689000800D500013Q0004D83Q00D500010020E6000900080017000689000900D500013Q0004D83Q00D500012Q00E3000900033Q0020E6000A000800172Q00F400090002000200264D000900D5000100020004D83Q00D500012Q00E3000900044Q007E0009000700092Q00E3000A00053Q000624000900D50001000A0004D83Q00D50001001206000900014Q0074000A00163Q00268E0009006E000100010004D83Q006E0001001255001700184Q00F300185Q00122Q001900193Q00122Q001A001A6Q0018001A000200122Q0019001B6Q0017001900024Q000A00173Q001217001700186Q00185Q00122Q0019001C3Q00122Q001A001D6Q0018001A00020012060019001E4Q00E50017001900022Q0022010B00173Q001217001700186Q00185Q00122Q0019001F3Q00122Q001A00206Q0018001A0002001206001900214Q00E50017001900022Q0022010C00173Q001217001700186Q00185Q00122Q001900223Q00122Q001A00236Q0018001A0002001206001900244Q00E50017001900022Q0022010D00173Q001206000900023Q00268E0009008D000100250004D83Q008D00010006F5001200770001000C0004D83Q00770001001255001700263Q0020E60017001700272Q00220118000C4Q00F40017000200022Q0022011200173Q0006F50013007E0001000D0004D83Q007E0001001255001700263Q0020E60017001700272Q00220118000D4Q00F40017000200022Q0022011300173Q0006F5001400850001000E0004D83Q00850001001255001700263Q0020E60017001700272Q00220118000E4Q00F40017000200022Q0022011400173Q0006F50015008C0001000F0004D83Q008C0001001255001700263Q0020E60017001700272Q00220118000F4Q00F40017000200022Q0022011500173Q001206000900283Q00268E000900AE000100020004D83Q00AE0001001255001700184Q00F300185Q00122Q001900293Q00122Q001A002A6Q0018001A000200122Q0019002B6Q0017001900024Q000E00173Q001217001700186Q00185Q00122Q0019002C3Q00122Q001A002D6Q0018001A00020012060019002E4Q00E50017001900022Q0022010F00173Q0006F5001000A60001000A0004D83Q00A60001001255001700263Q0020E60017001700272Q00220118000A4Q00F40017000200022Q0022011000173Q0006F5001100AD0001000B0004D83Q00AD0001001255001700263Q0020E60017001700272Q00220118000B4Q00F40017000200022Q0022011100173Q001206000900253Q00268E0009004B000100280004D83Q004B00012Q0074001600163Q0020E6001700080017000639001000B6000100170004D83Q00B60001001206001600023Q0004D83Q00D000010020E6001700080017000639001100BB000100170004D83Q00BB0001001206001600253Q0004D83Q00D000010020E6001700080017000639001200C0000100170004D83Q00C00001001206001600283Q0004D83Q00D000010020E6001700080017000639001300C5000100170004D83Q00C500010012060016002F3Q0004D83Q00D000010020E6001700080017000639001400CA000100170004D83Q00CA0001001206001600303Q0004D83Q00D000010020E6001700080017000639001500CF000100170004D83Q00CF0001001206001600313Q0004D83Q00D000010020E6001600080017000689001600D500013Q0004D83Q00D500012Q0018011600023Q0004D83Q00D500010004D83Q004B0001001255000900093Q00208B00090009003200202Q00090009003300202Q00090009003400202Q00090009003500202Q00090009003600062Q000900492Q013Q0004D83Q00492Q01001206000A00014Q0074000B000C3Q00268E000A00F7000100010004D83Q00F70001001255000D000F3Q00206A000D000D00104Q000E5Q00122Q000F00373Q00122Q001000386Q000E001000024Q000D000D000E00062Q000B00EF0001000D0004D83Q00EF00012Q00E3000D5Q001206000E00393Q001206000F003A4Q00E5000D000F00022Q0022010B000D3Q001255000D00263Q0020E6000D000D003B2Q0022010E000B4Q00F4000D000200020006EA000C00F60001000D0004D83Q00F60001001206000C00013Q001206000A00023Q00268E000A00DF000100020004D83Q00DF0001000EDE000100492Q01000C0004D83Q00492Q01001206000D00014Q0074000E000F3Q00268E000D000F2Q0100020004D83Q000F2Q01000689000F00492Q013Q0004D83Q00492Q010012550010003C3Q0020E600100010003D2Q0022011100034Q00F4001000020002000639000F00492Q0100100004D83Q00492Q012Q00E3001000034Q00220111000F4Q00F400100002000200264D001000492Q01002E0004D83Q00492Q010012060010003E4Q0018011000023Q0004D83Q00492Q0100268E000D00FD000100010004D83Q00FD00010012550010003F3Q001223011100253Q00122Q001200263Q00202Q0012001200404Q0013000B6Q001200136Q00103Q00024Q000E00103Q00062Q000F00202Q01000E0004D83Q00202Q01001255001000263Q0020E60010001000272Q00220111000E4Q00F40010000200022Q0022010F00103Q001206000D00023Q0004D83Q00FD00010004D83Q00492Q010004D83Q00DF00010004D83Q00492Q01000EDE000100492Q0100030004D83Q00492Q01001255000800413Q0020E60008000800422Q0022010900034Q00F4000800020002000689000800492Q013Q0004D83Q00492Q012Q00E3000800044Q007E0008000700082Q00E3000900053Q000624000800492Q0100090004D83Q00492Q012Q00E3000800064Q00E3000900074Q00F400080002000200264E0008003D2Q0100430004D83Q003D2Q012Q00E3000800064Q00E3000900074Q00F40008000200022Q00E3000900053Q000624000800492Q0100090004D83Q00492Q012Q00E3000800084Q00E3000900094Q00F400080002000200264E000800482Q0100430004D83Q00482Q012Q00E3000800084Q00E3000900094Q00F40008000200022Q00E3000900053Q000624000800492Q0100090004D83Q00492Q012Q0018010300023Q001206000800014Q0018010800023Q0004D83Q00552Q0100268E00010002000100010004D83Q000200012Q0074000200023Q0020E600033Q0002000689000300532Q013Q0004D83Q00532Q010020E600023Q0002001206000100023Q0004D83Q000200012Q00CF3Q00017Q002B3Q00028Q00026Q00104003063Q00435F4974656D030C3Q004765744974656D436F756E7403063Q0073656C656374027Q0040030B3Q004765744974656D496E666F03123Q004765744974656D496E666F496E7374616E74026Q00F03F03043Q006D6174682Q033Q00616273026Q002440026Q001440026Q000840026Q001840026Q001C4003183Q004C6567656E6461727953652Q74696E6773436C612Q73696303083Q0053652Q74696E6773030D3Q00ACEBEE9CAE02AF2C86F5DCA1A403083Q0043E8BBBDCCC176C6030F3Q00BF2BB8303E10EA8F6E852Q2F0BE08503073Q008FEB4ED5405B6203143Q00476574496E76656E746F72794974656D4C696E6B03063Q009D4485F075A403063Q00D6ED28E48910026Q002A4003063Q0095EFEEC006B403063Q00C6E5838FB963026Q002C4003063Q004180A96A549E03043Q001331ECC8026Q00304003063Q00EE3BF7AEE1A803063Q00DA9E5796D784026Q00314003063Q00EB12D8FB333003073Q00AD9B7EB9825642026Q002E4003063Q00F5AABBDE8DFE03063Q008C85C6DAA7E803073Q00435F5370652Q6C030D3Q0049735370652Q6C557361626C650001FE3Q0006893Q00FD00013Q0004D83Q00FD00012Q00222Q016Q003F00028Q000300016Q0002000200024Q000300016Q000400016Q00030002000200062Q000300D700013Q0004D83Q00D70001000EDE000100D7000100010004D83Q00D700012Q00E3000400024Q007E0004000300042Q00E3000500033Q000624000400D7000100050004D83Q00D70001001206000400014Q0074000500133Q00268E00040047000100020004D83Q00470001001255001400033Q0020E60014001400042Q0022011500124Q00F40014000200020006EA0013001D000100140004D83Q001D0001001206001300013Q000EDE000100D7000100130004D83Q00D70001001206001400014Q0074001500163Q00268E00140033000100010004D83Q00330001001255001700053Q001223011800063Q00122Q001900033Q00202Q0019001900074Q001A00126Q0019001A6Q00173Q00024Q001500173Q00062Q00160032000100150004D83Q00320001001255001700033Q0020E60017001700082Q0022011800154Q00F40017000200022Q0022011600173Q001206001400093Q00268E00140021000100090004D83Q00210001000689001600D700013Q0004D83Q00D700010012550017000A3Q0020E600170017000B2Q0022011800014Q00F4001700020002000639001600D7000100170004D83Q00D700012Q00E3001700014Q0022011800164Q00F400170002000200264D001700D70001000C0004D83Q00D700010012060017000D4Q0018011700023Q0004D83Q00D700010004D83Q002100010004D83Q00D7000100268E00040066000100060004D83Q006600010006F5000D0050000100070004D83Q00500001001255001400033Q0020E60014001400082Q0022011500074Q00F40014000200022Q0022010D00143Q0006F5000E0057000100080004D83Q00570001001255001400033Q0020E60014001400082Q0022011500084Q00F40014000200022Q0022010E00143Q0006F5000F005E000100090004D83Q005E0001001255001400033Q0020E60014001400082Q0022011500094Q00F40014000200022Q0022010F00143Q0006F5001000650001000A0004D83Q00650001001255001400033Q0020E60014001400082Q00220115000A4Q00F40014000200022Q0022011000143Q0012060004000E3Q00268E000400920001000E0004D83Q009200012Q0074001100113Q000639000B006D000100010004D83Q006D0001001206001100093Q0004D83Q00800001000639000C0071000100010004D83Q00710001001206001100063Q0004D83Q00800001000639000D0075000100010004D83Q007500010012060011000E3Q0004D83Q00800001000639000E0079000100010004D83Q00790001001206001100023Q0004D83Q00800001000639000F007D000100010004D83Q007D00010012060011000F3Q0004D83Q0080000100063900100080000100010004D83Q00800001001206001100103Q0006890011008300013Q0004D83Q008300012Q0018011100023Q001255001400113Q00206A0014001400124Q001500043Q00122Q001600133Q00122Q001700146Q0015001700024Q00140014001500062Q00120091000100140004D83Q009100012Q00E3001400043Q001206001500153Q001206001600164Q00E50014001600022Q0022011200143Q001206000400023Q00268E000400B5000100010004D83Q00B50001001255001400174Q00F3001500043Q00122Q001600183Q00122Q001700196Q00150017000200122Q0016001A6Q0014001600024Q000500143Q001217001400176Q001500043Q00122Q0016001B3Q00122Q0017001C6Q0015001700020012060016001D4Q00E50014001600022Q0022010600143Q001217001400176Q001500043Q00122Q0016001E3Q00122Q0017001F6Q001500170002001206001600204Q00E50014001600022Q0022010700143Q001217001400176Q001500043Q00122Q001600213Q00122Q001700226Q001500170002001206001600234Q00E50014001600022Q0022010800143Q001206000400093Q00268E00040014000100090004D83Q00140001001255001400174Q00F3001500043Q00122Q001600243Q00122Q001700256Q00150017000200122Q001600266Q0014001600024Q000900143Q001217001400176Q001500043Q00122Q001600273Q00122Q001700286Q0015001700020012060016000C4Q00E50014001600022Q0022010A00143Q0006F5000B00CE000100050004D83Q00CE0001001255001400033Q0020E60014001400082Q0022011500054Q00F40014000200022Q0022010B00143Q0006F5000C00D5000100060004D83Q00D50001001255001400033Q0020E60014001400082Q0022011500064Q00F40014000200022Q0022010C00143Q001206000400063Q0004D83Q00140001000EDE000100FB000100010004D83Q00FB0001001255000400293Q0020E600040004002A2Q0022010500014Q00F4000400020002000689000400FB00013Q0004D83Q00FB00012Q00E3000400024Q007E0004000200042Q00E3000500033Q000624000400FB000100050004D83Q00FB00012Q00E3000400054Q00E3000500064Q00F400040002000200264E000400EF0001002B0004D83Q00EF00012Q00E3000400054Q00E3000500064Q00F40004000200022Q00E3000500033Q000624000400FB000100050004D83Q00FB00012Q00E3000400074Q00E3000500084Q00F400040002000200264E000400FA0001002B0004D83Q00FA00012Q00E3000400074Q00E3000500084Q00F40004000200022Q00E3000500033Q000624000400FB000100050004D83Q00FB00012Q00182Q0100023Q001206000400014Q0018010400024Q00CF3Q00017Q00083Q00028Q00026Q00F03F03063Q004D617844707303053Q005370652Q6C027Q004003053Q00466C61677303053Q0070616972732Q0100363Q0012063Q00014Q0074000100023Q00268E3Q0015000100020004D83Q00150001001255000300033Q0006890003001300013Q0004D83Q00130001001255000300033Q0020E60003000300040006890003001300013Q0004D83Q00130001001255000300033Q0020E6000300030004000EDE00010013000100030004D83Q0013000100268E00010013000100010004D83Q00130001001255000300033Q0020E6000100030004001206000200013Q0012063Q00053Q00268E3Q002D000100010004D83Q002D0001001206000100013Q001255000300033Q0006890003002C00013Q0004D83Q002C0001001255000300033Q0020E60003000300060006890003002C00013Q0004D83Q002C0001001255000300073Q001255000400033Q0020E60004000400062Q00A60003000200050004D83Q002A000100268E0007002A000100080004D83Q002A000100264E0006002A000100010004D83Q002A00012Q00222Q0100063Q0004D83Q002C000100069C00030024000100020004D83Q002400010012063Q00023Q000E2C0005000200013Q0004D83Q000200012Q00E300036Q0023000400016Q0003000200024Q000200036Q000200023Q00044Q000200012Q00CF3Q00017Q00",
    GetFEnv(), ...);
