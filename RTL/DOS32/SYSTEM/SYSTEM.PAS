{----------------------------------------------------------------------------}
{                    Pascal Pro Runtime Library                              }
{                        (c) Copyright 1997-1999                             }
{                            System Unit                                     }
{                                        Iggor Khachko - hachko@icl.kazan.su }
{----------------------------------------------------------------------------}


unit System;

interface

{$IFNDEF DOS32}
{$ERROR Must be DOS32 target}
{$ENDIF}

{$IFNDEF PPRO}
{$ERROR Requires Pascal Pro compiler}
{$ENDIF}

const
  MinInt = -32768;
  MaxInt = 32767;


type
  ShortInt = -128..127;
  Integer = MinInt..MaxInt;
  LongInt = $80000000..$7FFFFFFF;
  Byte = 0..255;
  Word = 0..65535;
  Cardinal = DWord;
  Char = #0..#255;
  Real = Extended;

  pChar = ^Char;

type
  FarPointer = record
    Offset: LongInt;
    Selector: Word;
  end;

const
  ExitCode: Word = 0;
  ExitProc: Pointer = nil;
  ErrorAddr: Pointer = nil;
  CmdLine: String = '';
  PrefixAddress: Pointer = nil;

var
  InOutRes: Integer;

procedure Halt;
procedure Halt( anExitCode: Byte);

procedure RunError( ErrorCode: Integer);
function IOResult: LongInt;


procedure FillChar( var Buf; Count: LongInt; Code: Byte);
procedure FillChar( var Buf; Count: LongInt; CharCode: Char);
procedure Move( var Source, Dest; ByteCount: LongInt);

procedure RealToString( Value: Extended; var S: String; Width, Digs: LongInt);
procedure UIntToString( Value: LongInt; var S: String; Width: LongInt);
procedure SIntToString( Value: LongInt; var S: String; Width: LongInt);


function Hi( W: Word): Byte;
function Lo( W: Word): Byte;
function Swap( W: Word): Byte;


function UpCase( C: Char): Char;
function LoCase( C: Char): Char;

function ParamCount: LongInt;
function ParamStr( Index: LongInt): String;

function CSeg: Word;
function DSeg: Word;
function SSeg: Word;
function SPtr: LongInt;

const
  RandSeed: LongInt = 0;

procedure Randomize;
function Random( Max: DWord): DWord;
function Random: Extended;


{$I STRINGH.INC}
{$I MATHH.INC}
{$I SETH.INC}
{$I VALH.INC}
{$I TEXTH.INC}
{$I FILEH.INC}
{$I DIRH.INC}
{$I HEAPH.INC}

var
  SaveInt00: FarPointer;
  SaveInt0C: FarPointer;
  SaveInt0D: FarPointer;
  SaveInt1B: Pointer;
  SaveInt21: FarPointer;
  SaveInt23: Pointer;

type
  RealModeCallRegisters = record
    case integer of
      0: (EDI, ESI, EBP, L1, EBX, EDX, ECX, EAX: LongInt);
      1: (DI, W1, SI, W2, BP, W3, W4, W5, BX, W6, DX, W7, CX, W8, AX, W9,
          Flags, ES, DS, FS, GS, IP, CS, SP, SS: Word);
      2: (B1: array [0..15] of Byte;
          BL, BH, B2, B3, DL, DH, B4, B5, CL, CH, B6, B7, AL, AH: Byte);
  end;


implementation

const
  TrueString: String[4] = 'true';
  FalseString: String[5] = 'false';

procedure Terminate; forward;

procedure ToASCIIZ( const S: String; P: Pointer); Assembler;
  asm
    mov esi, dword ptr [S]
    mov edi, dword ptr [P]
    lodsb
    movzx ecx, al
    jcxz @@1
    rep movsb
  @@1:
    xor al, al
    stosb
  end;

procedure FromASCIIZ( P: Pointer; var S: String); Assembler;
  asm
    mov edi, dword ptr [S]
    mov esi, dword ptr [P]
    inc edi
    xor ecx, ecx

  @@loop:
    lodsb
    or al, al
    jz @@end_loop
    cmp ecx, 255
    jae @@end_loop
    stosb
    inc ecx
    jmp @@loop

  @@end_loop:
    mov edi, dword ptr [S]
    mov byte ptr [edi], cl
  end;

function IOResult: LongInt;
  begin
    IOResult := InOutRes;
  end;

const
  DivisionByZero                = 200;
  StackFault                    = 202;
  HeapOverflow                  = 203;
  InvalidPointerOperation       = 204;
  ObjectNotInitialized          = 210;
  GeneralProtectionFault        = 216;
  ErrorAllocatingHeap           = 255;

procedure RunError( ErrorCode: Integer); assembler;
  asm
    mov ax, ErrorCode
    mov ExitCode, ax
    mov eax, dword ptr [ebp + 4]
    mov ErrorAddr, eax
    jmp Terminate
  end;

procedure Halt; assembler;
  asm
    xor eax, eax
    call Terminate
  end;

procedure Halt( anExitCode: Byte); assembler;
  asm
    movzx eax, anExitCode
    mov ExitCode, ax
    xor eax, eax
    call Terminate
  end;


procedure FillChar( var Buf; Count: LongInt; Code: Byte); Assembler;
  asm
      mov edi, dword ptr [Buf]
      or edi, edi
      jz @@1
      mov ecx, Count
      or ecx, ecx
      jz @@1
      mov al, Code
      rep stosb
  @@1:
  end;

procedure FillChar( var Buf; Count: LongInt; CharCode: Char); Assembler;
  asm
      mov edi, dword ptr [Buf]
      or edi, edi
      jz @@1
      mov ecx, Count
      or ecx, ecx
      jz @@1
      mov al, CharCode
      rep stosb
  @@1:
  end;

procedure Move( var Source, Dest; ByteCount: LongInt); assembler;
  asm
    mov esi, dword ptr [source]
    mov edi, dword ptr [Dest]
    mov ecx, ByteCount
    jcxz @@1
    cmp edi, esi
    ja @@2
    cld
    rep movsb
    jmp @@1
  @@2:
    add esi, ecx
    dec esi
    add edi, ecx
    dec edi
    std
    rep movsb
    cld
  @@1:
  end;


procedure SIntToStr( Value: LongInt; var S: String); assembler;
  asm
      mov eax, Value
      xor edi, edi
      cmp eax, 0
      jge @@greater
      neg eax
      inc edi
    @@greater:
      mov esi, dword ptr [S]
      mov byte ptr [esi], 0
      mov ebx, 10

    @@beg:
      or eax, eax
      jz @@exit
      xor edx, edx
      idiv ebx
      add edx, 48
      movzx ecx, byte ptr [esi]

    @@begloop:
      jcxz  @@endloop
      mov dh, byte ptr [esi + ecx]
      mov byte ptr [esi + ecx + 1], dh
      dec ecx
      jmp @@begloop
    @@endloop:

      mov byte ptr [esi + 1], dl
      inc byte ptr [esi]
      jmp  @@beg
    @@exit:
      cmp byte ptr [esi], 0
      jnz @@notzero
      mov word ptr [esi], $3001
    @@notzero:
      or edi, edi
      jz @@notnegative

      movzx ecx, byte ptr [esi]
    @@begloop2:
      jcxz  @@endloop2
      mov dh, byte ptr [esi + ecx]
      mov byte ptr [esi + ecx + 1], dh
      dec ecx
      jmp @@begloop2
    @@endloop2:
      mov byte ptr [esi + 1], 45
      inc byte ptr [esi]
    @@notnegative:
  end;

procedure UIntToStr( Value: LongInt; var S: String); assembler;
  asm
      mov eax, Value
      mov esi, dword ptr [S]
      mov byte ptr [esi], 0
      mov ebx, 10

    @@beg:
      or eax, eax
      jz @@exit
      xor edx, edx
      idiv ebx
      add edx, 48
      movzx ecx, byte ptr [esi]

    @@begloop:
      jcxz  @@endloop
      mov dh, byte ptr [esi + ecx]
      mov byte ptr [esi + ecx + 1], dh
      dec ecx
      jmp @@begloop
    @@endloop:

      mov byte ptr [esi + 1], dl
      inc byte ptr [esi]
      jmp  @@beg
    @@exit:
      cmp byte ptr [esi], 0
      jnz @@notzero
      mov word ptr [esi], $3001
    @@notzero:
  end;


{
  Power10
In:
  ST(0) - Value
  EAX   - exp
Out:
  St(0) - Value * 10^exp
}
procedure Power10; assembler;
  asm
    test eax, eax
    jl  @@Neg
    jz  @@exit
    cmp eax,5120
    jge @@Inf
    mov edx, eax
    and edx, $01F
    lea edx, [ edx+edx*4]
    fld tbyte ptr [ @@tab0 + edx*2]
    fmulp

    shr eax,5
    jz  @@Exit

    mov edx,eax
    and edx,$0F
    jz  @@Skip2ndMul
    lea edx, [ edx+edx*4]
    fld tbyte ptr [ @@tab1-10 + edx*2]
    fmulp

@@Skip2ndMul:
    shr eax,4
    jz  @@exit
    lea eax, [ eax+eax*4]
    fld tbyte ptr [ @@tab2-10 + eax*2]
    fmulp
    jmp @@Exit

@@Neg:
    neg eax
    cmp eax,5120
    jge @@Zero
    mov edx, eax
    and edx, $01F
    lea edx, [ edx+edx*4]
    fld tbyte ptr [ @@tab0 + edx*2]
    fdivp

    shr eax, 5
    jz  @@Exit

    mov edx,eax
    and edx, $0F
    jz  @@Skip2ndDiv
    lea edx, [ edx+edx*4]
    fld tbyte ptr [ @@tab1-10 + edx*2]
    fdivp

@@Skip2ndDiv:

    shr eax, 4
    jz  @@Exit
    lea eax, [ eax+eax*4]
    fld tbyte ptr [ @@tab2-10 + eax*2]
    fdivp
    jmp @@Exit

@@tab0: DT      3FFF8000000000000000R   { 10**0 }
        DT      4002A000000000000000R   { 10**1 }
        DT      4005C800000000000000R   { 10**2 }
        DT      4008FA00000000000000R   { 10**3 }
        DT      400C9C40000000000000R   { 10**4 }
        DT      400FC350000000000000R   { 10**5 }
        DT      4012F424000000000000R   { 10**6 }
        DT      40169896800000000000R   { 10**7 }
        DT      4019BEBC200000000000R   { 10**8 }
        DT      401CEE6B280000000000R   { 10**9 }
        DT      40209502F90000000000R   { 10**10 }
        DT      4023BA43B74000000000R   { 10**11 }
        DT      4026E8D4A51000000000R   { 10**12 }
        DT      402A9184E72A00000000R   { 10**13 }
        DT      402DB5E620F480000000R   { 10**14 }
        DT      4030E35FA931A0000000R   { 10**15 }
        DT      40348E1BC9BF04000000R   { 10**16 }
        DT      4037B1A2BC2EC5000000R   { 10**17 }
        DT      403ADE0B6B3A76400000R   { 10**18 }
        DT      403E8AC7230489E80000R   { 10**19 }
        DT      4041AD78EBC5AC620000R   { 10**20 }
        DT      4044D8D726B7177A8000R   { 10**21 }
        DT      4048878678326EAC9000R   { 10**22 }
        DT      404BA968163F0A57B400R   { 10**23 }
        DT      404ED3C21BCECCEDA100R   { 10**24 }
        DT      405284595161401484A0R   { 10**25 }
        DT      4055A56FA5B99019A5C8R   { 10**26 }
        DT      4058CECB8F27F4200F3AR   { 10**27 }
        DT      405C813F3978F8940984R   { 10**28 }
        DT      405FA18F07D736B90BE5R   { 10**29 }
        DT      4062C9F2C9CD04674EDFR   { 10**30 }
        DT      4065FC6F7C4045812296R   { 10**31 }

@@tab1: DT      40699DC5ADA82B70B59ER   { 10**32 }
        DT      40D3C2781F49FFCFA6D5R   { 10**64 }
        DT      413DEFB3AB16C59B14A3R   { 10**96 }
        DT      41A893BA47C980E98CE0R   { 10**128 }
        DT      4212B616A12B7FE617AAR   { 10**160 }
        DT      427CE070F78D3927556BR   { 10**192 }
        DT      42E78A5296FFE33CC930R   { 10**224 }
        DT      4351AA7EEBFB9DF9DE8ER   { 10**256 }
        DT      43BBD226FC195C6A2F8CR   { 10**288 }
        DT      442681842F29F2CCE376R   { 10**320 }
        DT      44909FA42700DB900AD2R   { 10**352 }
        DT      44FAC4C5E310AEF8AA17R   { 10**384 }
        DT      4564F28A9C07E9B09C59R   { 10**416 }
        DT      45CF957A4AE1EBF7F3D4R   { 10**448 }
        DT      4639B83ED8DC0795A262R   { 10**480 }

@@tab2: DT      46A3E319A0AEA60E91C7R   { 10**512 }
        DT      4D48C976758681750C17R   { 10**1024 }
        DT      53EDB2B8353B3993A7E4R   { 10**1536 }
        DT      5A929E8B3B5DC53D5DE5R   { 10**2048 }
        DT      61378CA554C020A1F0A6R   { 10**2560 }
        DT      67DBF9895D25D88B5A8BR   { 10**3072 }
        DT      6E80DD5DC8A2BF27F3F8R   { 10**3584 }
        DT      7525C46052028A20979BR   { 10**4096 }
        DT      7BCAAE3511626ED559F0R   { 10**4608 }

@@infval:DT      7FFF8000000000000000R

@@Inf:
    fld tbyte ptr [ @@infval]
    jmp @@Exit

@@Zero:
    fldz
@@Exit:
  end;

procedure Scale; assembler;
  var
    Val: Extended;
  asm
  @@Scale:
    push ecx
    push edx
    xor ecx, ecx

  @@Loop:
    fld  st(0)
    fstp tbyte ptr [ Val]
    mov ax, word ptr [Val + 8]
    and ax, ax
    jz  @@IsZero

  @@InnerLoop:
    sub ax, $3FFF
    mov dx, $4D10
    imul dx
    movsx eax, dx
    neg eax
    jz  @@Exit
    sub ecx, eax
    call Power10
    jmp @@Loop

  @@IsZero:
    cmp dword ptr [ Val], 0
    jnz @@InnerLoop
    cmp dword ptr [ Val + 4], 0
    jnz @@InnerLoop

  @@Exit:
    mov eax, ecx
    pop edx
    pop ecx
  end;

procedure DecodeValue; assembler;
  var
    Buf: array [0..9] of Byte;
  asm
    push ecx
    push edx
    mov ecx, eax
    mov byte ptr [edi], '0'
    fmul qword ptr [ @@e17]
    frndint
    fcom qword ptr [ @@e18]
    fstsw ax
    sahf
    jb  @@1
    fsub qword ptr [ @@e18]
    mov byte ptr [edi], '1'
  @@1:
    fbstp tbyte ptr [Buf]
    mov edx, 8
    inc edi
  @@Loop:
    fwait
    mov al, byte ptr [ Buf + edx]
    mov ah, al
    shr al, 4
    and ah, $0F
    add ax, '00'
    stosw
    dec edx
    jns @@Loop

    sub ecx, 18
    jl  @@2
    mov al, '0'
    rep stosb
    jmp @@Exit

    add edi, ecx
    cmp byte ptr [edi], '5'
    jl  @@Exit
  @@2:
    dec edi
    inc byte ptr [edi]
    cmp byte ptr [edi], '9'
    jle @@Exit
    mov byte ptr [edi], '0'
    jmp @@2

  @@e17: DQ 1.0e17
  @@e18: DQ 1.0e18

  @@Exit:
    pop edx
    pop ecx
  end;

procedure RealToStr( Value: Extended; var S: String; Digs: LongInt); assembler;
  const
    NanStr: String[3] = 'Nan';
    PlusInfStr: String[4] = '+inf';
    MinusInfStr: String[4] = '-inf';
  var
    Buf: String;
  asm
    cld
    fld Value
    mov edx, Digs
    movzx eax, word ptr [Value + 8]
    mov ecx, eax
    shr ecx, 15
    and ax, $7FFF
    cmp ax, $7FFF
    je  @@NanInf
    fabs

    and edx, edx
    jge @@Fixed
    call Scale

  @@Scientific:
    neg edx
    cmp edx, 2
    jge @@1
    mov edx, 2
  @@1:
    cmp edx, 18
    jle @@2
    mov edx, 18
  @@2:
    push eax
    mov eax, edx
    lea edi, Buf
    call DecodeValue

    mov edi, dword ptr [ S]
    mov ebx, edi
    inc edi

    or  cl, cl
    jz  @@3
    mov al, '-'
    stosb
  @@3:
    pop eax
    mov ecx, edx
    lea esi, Buf
    cmp byte ptr [ esi], '0'
    jz @@4
    inc eax
    dec esi
  @@4:
    inc esi
    movsb
    dec ecx
    mov byte ptr [edi], '.'
    inc edi
    dec ecx
    rep movsb
    mov byte ptr [edi], 'E'
    inc edi
    mov cl, '+'
    and eax, eax
    jge @@5
    mov cl, '-'
    neg eax
  @@5:
    mov byte ptr [edi], cl
    inc edi
    xor edx, edx
    mov cx, 10
    div cx
    add dl, '0'
    mov byte ptr [edi+3], dl
    xor edx, edx
    mov cx, 10
    div cx
    add dl, '0'
    mov byte ptr [edi+2], dl
    xor edx, edx
    mov cx, 10
    div cx
    add dl, '0'
    mov byte ptr [edi+1], dl
    add al, '0'
    stosb
    lea eax, [ edi + 2]
    sub eax, ebx
    mov edi, ebx
    stosb
    jmp @@Exit

  @@Fixed:
    cmp edx, 18
    jle @@@1
    mov edx, 18
  @@@1:
    fcom  qword ptr [ @@e1]
    fstsw ax
    sahf
    mov eax, 0
    jb @@@2
    call Scale
    cmp eax, 35
    jle @@@2
    mov edx, -18
    jmp @@Scientific
  @@@2:
    inc eax
    push eax
    add eax, edx
    lea edi, Buf
    call DecodeValue
    pop eax
    lea esi, Buf
    cmp byte ptr [esi], '0'
    jz  @@@3
    inc eax
    dec esi
  @@@3:
    inc esi
    mov ebx, ecx
    add ecx, eax
    and edx, edx
    jz  @@@4
    inc ecx
    add ecx, edx
  @@@4:
    mov edi, dword ptr [ S]
    mov byte ptr [ edi], cl
    inc edi
    test ebx, ebx
    jz  @@@5
    mov byte ptr [ edi], '-'
    inc edi
  @@@5:
    xchg eax, ecx
    rep movsb
    and edx, edx
    jz  @@@6
    mov byte ptr [ edi], '.'
    inc edi
    mov ecx, edx
    rep movsb
  @@@6:
    jmp @@Exit

  @@e1: DQ 1.0e1

  @@NanInf:
    cmp dword ptr [ Value + 4], $80000000
    lea esi, NanStr
    jnz @@Copy
    dec ecx
    lea esi, PlusInfStr
    jnz @@Copy
    lea esi, MinusInfStr
  @@Copy:
    mov edi, dword ptr [ S]
    lodsb
    movzx ecx, al
    stosb
    rep movsb

  @@Exit:
  end;



procedure RenameFile( OldName, NewName: Pointer); Assembler;
  asm
    mov edx, OldName
    mov edi, NewName
    mov ax, $5600
    int $21
    jnc @@exit
    mov InOutRes, ax
  @@exit:
  end;

procedure DeleteFile( FileName: Pointer); Assembler;
  asm
    mov ecx, FileName
    mov ax, $4100
    int $21
    jnc @@exit
    mov InOutRes, ax
  @@exit:
  end;


function OpenFile( Name: Pointer; Mode: Word): Word; Assembler;
  asm
    movzx eax, Mode
    mov edx, Name
    int $21
    jnc @@exit
    mov InOutRes, ax
    xor eax, eax
  @@exit:
  end;

procedure CloseFile( Handle: Word); Assembler;
  asm
    mov ah, $3E
    movzx ebx, Handle
    int $21
    jnc @@exit
    mov InOutRes, ax
  @@exit:
  end;

function WriteBufToFile( Handle: Word; Buf: Pointer;
    Size: LongInt): LongInt; assembler;
  asm
      movzx ebx, handle
      mov edx, dword ptr [buf]
      mov ecx, size
      mov ah, $40
      int $21
  end;

function ReadFromFile( Handle: Word; Buf: Pointer; Size: LongInt): LongInt; assembler;
  asm
      movzx ebx, handle
      mov edx, dword ptr [buf]
      mov ecx, size
      mov ah, $3f
      int $21
      jnc @@exit
      xor eax, eax
  @@exit:
  end;


procedure InsertSpaces( var S: String; Len: LongInt);
  var
    Str: String;
  begin
    if Len > 255 then Len := 255;
    if Length( S) < Len then
      begin
        FillChar( Str[ 1], Len - Byte( S[0]), ' ');
        Str[0] := Char( Len - Byte(S[0]));
        Insert( Str, S, 1);
      end;
  end;



procedure RealToString( Value: Extended; var S: String; Width, Digs: LongInt); 'realtostring';
  begin
    RealToStr( Value, S, Digs);
    InsertSpaces( S, Width);
  end;

procedure UIntToString( Value: LongInt; var S: String; Width: LongInt); 'uinttostring';
  begin
    UIntToStr( Value, S);
    InsertSpaces( S, Width);
  end;

procedure SIntToString( Value: LongInt; var S: String; Width: LongInt); 'sinttostring';
  begin
    SIntToStr( Value, S);
    InsertSpaces( S, Width);
  end;


function Hi( W: Word): Byte; assembler;
  asm
    movzx eax, W
    shr eax, 8
  end;

function Lo( W: Word): Byte; assembler;
  asm
    movzx eax, W
    and eax, $FF
  end;

function Swap( W: Word): Byte; assembler;
  asm
    movzx eax, W
    xchg al, ah
  end;


function UpCase( C: Char): Char; assembler;
  asm
    mov al, c
    cmp al, 'a'
    jb  @@exit
    cmp al, 'z'
    ja  @@exit
    sub al, 32
  @@exit:
  end;

function LoCase( C: Char): Char; assembler;
  asm
    mov al, c
    cmp al, 'A'
    jb  @@exit
    cmp al, 'Z'
    ja  @@exit
    add al, 32
  @@exit:
  end;


function ParamCount: LongInt; assembler;
  asm
    lea esi, CmdLine
    lodsb
    movzx ecx, al
    xor edx, edx

  @@1:
    jcxz @@3
    lodsb
    dec ecx
    cmp al, ' '
    jne @@1

    inc edx
  @@2:
    jcxz @@3
    lodsb
    dec ecx
    cmp al, ' '
    je  @@2
    jmp @@1

  @@3:
    mov eax, edx
  end;

function ParamStr( Index: LongInt): String; assembler;
  asm
    mov edx, Index
    or  edx, edx
    jne @@CmdLine

    mov eax, $EE02
    int $31
    mov esi, ecx
    mov edi, dword ptr [@Result]
    inc edi
    mov edx, edi
    cld

  @@1:
    lodsb
    or  al, al
    je  @@2
    stosb
    jmp @@1

  @@2:
    mov eax, edi
    sub eax, edx
    mov edi, edx
    dec edi
    stosb
    jmp @@Exit

  @@CmdLine:
    cld
    mov edi, dword ptr [@Result]

    lea esi, CmdLine
    lodsb
    movzx ecx, al

  @@11:
    jcxz @@15
    lodsb
    dec ecx
    cmp al, ' '
    jne @@11

  @@12:
    jcxz @@15
    lodsb
    dec ecx
    cmp al, ' '
    je  @@12

    dec edx
    jne @@11

    inc edi
    mov edx, edi

  @@13:
    stosb
    jcxz @@14
    lodsb
    dec ecx
    cmp al, ' '
    jne @@13

  @@14:
    mov eax, edi
    sub eax, edx
    mov edi, edx
    dec edi
    stosb
    jmp @@Exit

  @@15:
    xor al, al
    stosb

  @@exit:
  end;


function CSeg: Word; assembler;
  asm
    mov ax, cs
    movzx eax, ax
  end;

function DSeg: Word; assembler;
  asm
    mov ax, ds
    movzx eax, ax
  end;

function SSeg: Word; assembler;
  asm
    mov ax, ss
    movzx eax, ax
  end;

function SPtr: LongInt; assembler;
  asm
    mov eax, esp
  end;


procedure Randomize; assembler;
  asm
    mov eax, $2C00
    int $21
    mov word ptr [ RandSeed], dx
    mov word ptr [ RandSeed + 2], cx
  end;

function GenerateNextRandom: DWord; assembler;
  asm
    mov eax, 134775813
    mul dword ptr [ RandSeed]
    inc eax
    mov dword ptr [ RandSeed], eax
  end;

function Random( Max: DWord): DWord; assembler;
  asm
    call GenerateNextRandom
    xor edx, edx
    div dword ptr [ Max]
    mov eax, edx
  end;

function Random: Extended; assembler;
  const
    LongDelta: Single = 2147483648.0;
    LongScale: LongInt = -32;
  asm
    call GenerateNextRandom
    fild LongScale
    fild RandSeed
    fadd LongDelta
    fscale
    fstp st(1)
    fwait
  end;


{$I STRING.INC}
{$I MATH.INC}
{$I SET.INC}
{$I VAL.INC}
{$I TEXT.INC}
{$I FILE.INC}
{$I DIR.INC}
{$I HEAP.INC}

const
{$IFDEF _RUSSIAN_}
  ErrorMessage: String[30] = 'Ошибка во время выполнения: ';
  ErrorMessageAddr: String[14] = ' по адресу ';
{$ENDIF}
{$IFDEF _ENGLISH_}
  ErrorMessage: String[30] = 'Runtime error: ';
  ErrorMessageAddr: String[ 4] = ' at ';
{$ENDIF}

procedure Terminate; 'terminate'; assembler;
  asm
    movzx eax, al
    push eax
  @@do_clean:
    mov eax, ExitProc
    or  eax, eax
    jz  @@cleared
    mov ExitProc, 0
    call eax
    jmp @@do_clean

  @@cleared:
    call DoneHeap
    pop eax
    or ax, ax
    jz @@NoError
    jmp @@Error

{$IFDEF _ENGLISH_}
  @@ErrorMessage:
    DB 'Runtime Error:   '
  @@ErrorCode:
    DB '0'
    DB ' at '
  @@ErrorAddr:
    DB '00000000'
    DB 13
    DB 10
    DB '$'
{$ENDIF}
{$IFDEF _RUSSIAN_}
  @@ErrorMessage:
    DB 'Ошибка во время выполнения:   '
  @@ErrorCode:
    DB '0'
    DB ' по адресу '
  @@ErrorAddr:
    DB '00000000'
    DB 13
    DB 10
    DB '$'
{$ENDIF}

  @@Error:
    mov edi, offset @@ErrorCode
    mov cx, 10
  @@Code_Loop:
    xor edx, edx
    div cx
    add dl, '0'
    mov byte ptr [edi], dl
    dec edi
    or  eax, eax
    jnz @@Code_Loop

    mov edi, offset @@ErrorAddr
    mov edx, ErrorAddr
    cld
  @@Addr_Loop:
    or  edx, edx
    jz  @@End_Loop
    mov eax, edx
    shr eax, 28
    shl edx, 4
    cmp al, 10
    jae @@A
    add al, '0'
    jmp @@MOV
  @@A:
    add al, 'A' - 10
  @@MOV:
    stosb
    jmp @@Addr_Loop

  @@End_Loop:
    mov edx, offset @@ErrorMessage
    mov eax, $0900
    int $21

  @@NoError:

    {mov ax, $0203
    xor bl, bl
    mov edx, dword ptr [SaveInt00]
    mov cx, word ptr [SaveInt00 + 4]
    int $31

    mov ax, $0203
    mov bl, $0C
    mov edx, dword ptr [SaveInt0C]
    mov cx, word ptr [SaveInt0C + 4]
    int $31

    mov ax, $0203
    mov bl, $0C
    mov edx, dword ptr [SaveInt0D]
    mov cx, word ptr [SaveInt0D + 4]
    int $31

    mov dx, word ptr [ SaveInt1B]
    mov cx, word ptr [ SaveInt1B + 2]
    mov eax, $0201
    mov bl, $1B
    int $31}

    {mov ax, $0205
    mov bl, $21
    mov edx, dword ptr [SaveInt21]
    mov cx, word ptr [SaveInt21 + 4]
    int $31}

    {mov dx, word ptr [ SaveInt23]
    mov cx, word ptr [ SaveInt23 + 2]
    mov eax, $0201
    mov bl, $23
    int $31}

    mov ax, ExitCode
    mov ah, $4c
    int $21
  end;

const
  messagectrlbreak: string = ' ctrl-break pressed '#13#10;
  doexit: word = 1;

procedure Int23Handler; assembler;
  asm
    mov eax, $4c00
    int $21
  end;


procedure CopyObject( Dest, VMT, Source: Pointer); 'copyobject'; assembler;
  asm
    mov eax, VMT
    or  eax, eax
    jz  @@exit
    mov ecx, dword ptr [eax]
    jcxz @@exit
    mov edx, dword ptr [eax + 4]
    add edx, ecx
    jnz @@exit
    mov edi, Dest
    or  edi, edi
    jz  @@exit
    mov esi, Source
    or  esi, esi
    jz  @@exit
    stosd
    add esi, 4
    rep stosw
    @@exit:
  end;


procedure DispatchVirtual; 'dispatchvirtual'; assembler;
  {
    Call virtual method
      input:
        ebx - self
        eax - virtual method index in vmt
  }
  asm
    or  ebx, ebx                { is self = nil }
    jz  @@error

    or  eax, eax
    jz  @@error                 { is method index = 0 }

    mov esi, dword ptr [ebx]    { esi := self^.VMT }
    or  esi, esi
    jz  @@error

    mov edx, dword ptr [esi]    { edx := sizeof }
    cmp edx, 0
    jl  @@error                 { is sizeof < 0 }

    mov ecx, dword ptr [esi + 4]    { ecx := -sizeof }
    cmp ecx, 0                  { is -sizeof > 0 }
    jg  @@error

    add ecx, edx                { ecx := ecx + edx ( -sizeof + sizeof ) }
    jnz @@error

    mov edx, dword ptr [esi + eax * 4 + 8]
    mov esp, ebp
    pop ebp
    jmp edx
  @@error:
    push ObjectNotInitialized
    call RunError
  end;

var
  RealRegisters: RealModeCallRegisters;

const
  CtrlBreakState: Byte = 0;

const
  Div0Mess: String = 'Division by zero'#13#10;

begin
  asm
      mov eax, $EE00
      int $31
      mov fs, bx

      mov eax, $EE02
      int $31
      mov PrefixAddress, esi
      add esi, $80
      movzx ecx, byte ptr [esi]
      lea edi, CmdLine
      inc ecx
      rep movsb
  @1:
      jmp @@2

  @@ExceptionHalt:
      mov ax, cs
      add ax, 8
      mov ds, ax
      mov es, ax
      movzx eax, ExitCode

      jmp Terminate

  @@Int00:
      push eax
      mov eax, DivisionByZero
      jmp @@Except

  @@Int0C:
      push eax
      mov eax, StackFault
      jmp @@Except

  @@Int0D:
      push eax
      mov eax, GeneralProtectionFault

  @@Except:
      push ebp
      push ds
      mov ebp, esp
      push eax
      mov ax, cs
      add ax, 8
      mov ds, ax
      pop eax
      mov ds:[ExitCode], ax
      mov eax, dword ptr [ebp + 24]
      mov ErrorAddr, eax
      mov dword ptr [ebp + 24], offset @@ExceptionHalt
      mov word ptr [ebp + 28], cs
      cmp dword ptr [ebp + 36], 2048
      jae @@Above
      mov dword ptr [ebp + 36], 2048
    @@Above:
      pop ds
      pop ebp
      pop eax
      retf

  @@Int23:
      cld
      lodsw
      mov word ptr es:[edi].RealModeCallRegisters.&IP, ax
      lodsw
      mov word ptr es:[edi].RealModeCallRegisters.&CS, ax
      lodsw
      mov word ptr es:[edi].RealModeCallRegisters.&FLAGS, ax
      add word ptr es:[edi].RealModeCallRegisters.&SP, 6
      mov es:[CtrlBreakState], 1
      iret

  @@Int21:
      pushf
      call pword ptr [SaveInt21]

      pushf
      push ds
      push eax
      mov ax, cs
      add ax, 8
      mov ds, ax
      cmp ds:[ CtrlBreakState], 0
      jz @@NotPressed
      mov ds:[ExitCode], 255
      mov es, ax
      xor eax, eax
      call Terminate

    @@NotPressed:
      pop eax
      pop ds
      popf
      retf 4

  @@2:

      {mov ax, $0204
      mov bl, 0
      int $31
      mov dword ptr [SaveInt00], edx
      mov word ptr [SaveInt00 + 4], cx

      mov ax, $0205
      mov bl, 0
      mov cx, cs
      mov edx, offset @@Int00
      int $31

      mov ax, $0204
      mov bl, $0C
      int $31
      mov dword ptr [SaveInt0C], edx
      mov word ptr [SaveInt0C + 4], cx

      {mov ax, $0205
      mov bl, $0C
      mov cx, cs
      mov edx, offset @@Int0C
      int $31}

      mov ax, $0204
      mov bl, $0D
      int $31
      mov dword ptr [SaveInt0D], edx
      mov word ptr [SaveInt0D + 4], cx

      mov ax, $0205
      mov bl, $0D
      mov cx, cs
      mov edx, offset @@Int0D
      int $31}

      mov ax, $0204
      mov bl, $21
      int $31
      mov dword ptr [SaveInt21], edx
      mov word ptr [SaveInt21 + 4], cx

      {mov ax, $0205
      mov bl, $21
      mov cx, cs
      mov edx, offset @@Int21
      int $31}

      {mov ax, $0200
      mov bl, $23
      int $31
      mov word ptr [SaveInt23], dx
      mov word ptr [SaveInt23 + 2], cx

      mov esi, offset @@int23
      mov edi, offset RealRegisters
      push ds
      push cs
      pop ds
      mov eax, $0303
      int $31
      mov eax, $0201
      mov bl, $23
      int $31
      pop ds

      mov ax, $0200
      mov bl, $1B
      int $31
      mov word ptr [SaveInt1B], dx
      mov word ptr [SaveInt1B + 2], cx}

  end;
  TextRec(Input).Handle:=0;
  TextRec(Input).Mode:=fmInput;
  TextRec(Input).InOutFunc := @TextInOut;
  TextRec(Input).FlushFunc := @TextInOut;
  TextRec(Input).BufPtr := @TextRec(Input).Buffer;
  TextRec(Input).BufSize := 128;
  TextRec(Input).BufPos := 0;
  TextRec(Input).BufEnd := 0;

  TextRec(Output).Handle:=1;
  TextRec(Output).Mode:=fmOutput;
  TextRec(Output).InOutFunc := @TextInOut;
  TextRec(Output).FlushFunc := @TextInOut;
  TextRec(Output).BufPtr := @TextRec(Output).Buffer;
  TextRec(Output).BufSize := 128;
  TextRec(Output).BufPos := 0;
  TextRec(Output).BufEnd := 0;

  InitHeap();
end.