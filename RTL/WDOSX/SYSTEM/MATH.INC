

function Trunc( R: Extended): longint; assembler;
  var
    Temp:  longint;
    TempWord,
    CtrlWord : word;
  asm
    fstcw word ptr [CtrlWord]
    mov   ax,word ptr [CtrlWord]
    {and   ax,$F3FF}
    or    ax,$0C00
    mov   word ptr [TempWord],ax
    fldcw word ptr [TempWord]

    fld   tbyte ptr [r]
    fistp dword ptr [Temp]

    fldcw word ptr [CtrlWord]
    mov eax, Temp
  end;

function Round( R: Extended): LongInt; assembler;
  var
    Temp:  longint;
    TempWord,
    CtrlWord : word;
  asm
    fstcw word ptr [CtrlWord]
    mov ax, CtrlWord
    and ax, $F3FF
    mov   word ptr [TempWord],ax
    fldcw word ptr [TempWord]

    fld   tbyte ptr [r]
    fistp dword ptr [Temp]

    fldcw word ptr [CtrlWord]
    mov eax, Temp
  end;

function Int( R: Extended): Extended; assembler;
  var
    TempWord,
    CtrlWord : word;
  asm
    fstcw word ptr [CtrlWord]
    mov   ax,word ptr [CtrlWord]
    {and   ax,$F3FF}
    or    ax,$0C00
    mov   word ptr [TempWord],ax
    fldcw word ptr [TempWord]

    fld   tbyte ptr [r]
    frndint

    fldcw word ptr [CtrlWord]
  end;

function Frac( R: Extended): Extended; assembler;
  var
    TempWord,
    CtrlWord : word;
  asm
    fstcw word ptr [CtrlWord]
    mov   ax,word ptr [CtrlWord]
    {and   ax,$F3FF}
    or    ax,$0C00
    mov   word ptr [TempWord],ax
    fldcw word ptr [TempWord]

    fld tbyte ptr [R]
    fld tbyte ptr [R]

    frndint
    fsub

    fldcw word ptr [CtrlWord]
  end;

function Exp( R: Extended): Extended; assembler;
  var
    CtrlWord, TempWord: Word;
  asm
    fld tbyte ptr [R]
    fldl2e
    fmulp
    fstcw CtrlWord
    fwait
    mov ax, CtrlWord
    and ax, $F3FF
    mov TempWord, ax
    fldcw TempWord
    fld st(0)
    frndint
    fldcw CtrlWord
    fxch st(1)
    fsub st, st(1)
    f2xm1
    fld1
    faddp
    fscale
    fstp st(1)
  end;

function Ln( R: Extended): Extended; assembler;
  asm
    fldln2
    fld tbyte ptr [R]
    fyl2x
  end;

