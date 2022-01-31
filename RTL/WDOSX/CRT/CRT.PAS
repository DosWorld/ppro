{                    GNU LESSER GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Full text of license:
 https://www.gnu.org/licenses/lgpl-3.0.en.html

 (c) Copyright 2022 DosWord
 (c) Copyright 1997-1998 Iggor Khachko - hachko@icl.kazan.su }

unit CRT;

interface

{$IFNDEF WDOSX}
{$ERROR Must be WDOSX target}
{$ENDIF}

{$IFNDEF PPRO}
{$ERROR Requires Pascal Pro compiler}
{$ENDIF}

const

{ Screen modes constants }

  BW40          = 0;
  CO40          = 1;
  BW80          = 2;
  CO80          = 3;
  Mono          = 7;
  Font8x8       = 256;

{ Color constants }

  Black         = 0;
  Blue          = 1;
  Green         = 2;
  Cyan          = 3;
  Red           = 4;
  Magenta       = 5;
  Brown         = 6;
  LightGray     = 7;

  DarkGray      = 8;
  LightBlue     = 9;
  LightGreen    = 10;
  LightCyan     = 11;
  LightRed      = 12;
  LightMagenta  = 13;
  Yellow        = 14;
  White         = 15;

  Blink         = 128;

var
  CheckBreak: Boolean;
  DirectVideo: Boolean;
  CheckEOF: Boolean;
  CheckSnow: Boolean;

  TextAttr: Byte;

  LastMode: Word;
  WindMin: Word;
  WindMax: Word;

{ Selects a specific text mode }
procedure TextMode( Mode: Word);

{ Selects the foreground character color }
procedure TextColor( Color: Byte);
{ Selects the background color }
procedure TextBackground( Color: Byte);
{ Selects a low-intensity characters }
procedure LowVideo;
{ Selects a high-intesity characters }
procedure HighVideo;
{ Selects the original text attrubute read from the cursor loaction at startup }
procedure NormVideo;

{ Defines a text window on the screen }
procedure Window( Left, Top, Right, Bottom: Byte);
{ Moves the cursor to specified position }
procedure GotoXY( X, Y: Byte);
{ Returns the X coordinate of the current cursor position }
function WhereX: Byte;
{ Returns the Y coordinate of the current cursor position }
function WhereY: Byte;

{ Clears whole text window }
procedure ClrScr;
{ Clears all character to the end of line }
procedure ClrEOL;

{ Inserts empty line at the cursor position }
procedure InsLine;
{ Delete the line containing the cursor }
procedure DelLine;

{ Determines if a key has been pressed }
function KeyPressed: Boolean;
{ Read a character from the keyboard }
function ReadKey: Char;

{ Assiciates the text file with CRT window }
procedure AssignCrt( var TextFile: Text);

{ Dellays a specifed number of milliseconds }
procedure Delay( ms: Word);
{}
procedure Sound( Hz: Word);
{}
procedure NoSound;

implementation

{const
  bs = #8;
  esc = #27;
  eof = #26;
  cr = #13;
  lf = #10;}

procedure SetCrtMode( Mode: Word); assembler;
  asm
    mov ax, Mode
    and byte ptr fs:[$400 + $87], $FE
    cmp al, 7
    je  @@1
    cmp al, 3
    jbe @@1
    mov al, 3
  @@1:
    push eax
    xor ah, ah
    int $10
    pop eax
    or  ah, ah
    jz  @@exit
    push ebp
    mov eax, $1112
    xor bl, bl
    int $10
    mov eax, $1130
    xor bh, bh
    mov dl, bh
    int $10
    pop ebp
    cmp dl, 42
    jnz @@exit
    or  byte ptr fs:[$400 + $87], 1
    mov eax, $0100
    mov ecx, $0600
    int $10
    mov ah, $12
    mov bl, $20
    int $10
  @@exit:
  end;

var
  CurScreenSize: Word;
  NormAttr: Byte;

procedure SetCrtVariables; assembler;
  asm
    mov ah, $0F
    int $10
    push eax
    push ebp
    push es
    mov eax, $1130
    xor bh, bh
    mov dl ,bh
    int $10
    pop es
    pop ebp
    pop eax
    xor cl, cl
    or  dl, dl
    jnz @@1
    mov dl, 24
    cmp al, 3
    ja  @@1
    inc cl
  @@1:
    mov dh, dl
    mov dl, ah
    dec dl
    xor ah, ah
    cmp dh, 24
    jbe @@2
    mov ah, 1
  @@2:
    mov LastMode, ax
    mov CurScreenSize, dx
    mov CheckSnow, cl
    mov DirectVideo, 1
    xor eax, eax
    mov WindMin, ax
    mov WindMax, dx
  end;

procedure TextMode( Mode: Word); assembler;
  asm
    movzx eax, Mode
    push eax
    call SetCRTMode
    call SetCRTVariables
    mov al, NormAttr
    mov TextAttr, al
  end;

const
  ScanCode: Char = #0;

function KeyPressed: Boolean; assembler;
  asm
    cmp ScanCode, 0
    jnz @@Pressed
    mov ah, $01
    int $16
    {xor al, al
    jz @@exit}
  @@Pressed:
    {mov al, 1}
    setnz al
  @@exit:
  end;

function ReadKey: Char; assembler;
  asm
    mov al, ScanCode
    or  al, al
    mov ScanCode, 0
    jnz  @@exit
    xor ah, ah
    int $16
    or  al, al
    jnz @@exit
    mov ScanCode, ah
  @@exit:
  end;


procedure DirectWrite( Buf: Pointer; Count: LongInt); assembler;
  asm
    {mov esi, Buf
    mov ecx, Count
    or ecx, ecx
    jz @@exit
    movzx ebx, word ptr fs:[$400 + $50]  { get cursor position }

    mov edi, $B8000
    movzx eax, bh                         { eax = line }
    mul word ptr fs:[$400 + $4A]
    movzx edx, bl
    add eax, edx
    shl eax, 1
    add edi, eax
    mov edx, ebx

    movzx ebx, word ptr fs:[$400 + $4A]
    sub bl, byte ptr [WindMax]
    add bl, byte ptr [WindMin]
    mov ah, TextAttr

  @@loop:
    lodsb
    cmp al, 7
    jz @@beep
    cmp al, 8
    jz @@bs
    cmp al, 10
    jz @@nl
    cmp al, 13
    jz @@cr

    inc dl
    cmp dl, byte ptr [WindMax]
    jbe @@1

    add edi, ebx
    inc dh
    cmp dh, byte ptr [WindMax + 1]
    jbe @@1
    dec dh
    push eax
    push edx
    push ecx
    mov eax, $0601
    mov bh, byte ptr [TextAttr]
    mov cx, [WindMin]
    mov dx, [WindMax]
    int $10
    pop ecx
    pop edx
    pop eax
    sub edi, 80

  @@1:
    stosw
    jmp @@ok

  @@beep:

  @@bs:

  @@nl:
    inc dh
    cmp dh, byte ptr [WindMax + 1]
    jbe @@ok
    dec dh
    push eax
    push edx
    push ecx
    mov eax, $0601
    mov bh, byte ptr [TextAttr]
    mov cx, [WindMin]
    mov dx, [WindMax]
    int $10
    pop ecx
    pop edx
    pop eax
    sub edi, 80
    jmp @@ok

  @@cr:
    xor dl, dl

  @@ok:
    or ecx, ecx
    jz @@loop

          mov   word ptr fs:[$0400+$50], dx {cursor position}
          xor eax, eax
          mov   al, dh
          mul   word ptr fs:[$0400+$4A]     {crt width}
          xor   dh, dh
          add   ax, dx
          movzx ecx, ax

          mov   dx, word ptr fs:[$0400+$63]  {address of video chip}
          mov   al, 14
          out   dx, al
          nop
          nop
          nop
          mov   al, ch
          inc   dx
          out   dx, al
          nop
          nop
          nop
          dec   dx
          mov   al, 15
          out   dx, al
          nop
          nop
          nop
          mov   al, cl
          inc   dx
          out   dx, al
                     
  @@exit:}
          mov   ecx, dword ptr [Count]
          mov   edi, dword ptr [Buf]

          movzx edx, word ptr fs:[$0400+$50] {cursor position}
          mov   ebx, edx
          mov   esi, edi
@11:
          mov   al, byte ptr [edi]

          cmp   al, 7  {bell}
          je    @12
          cmp   al, 8  {backspace}
          je    @13
          cmp   al, 10 {carriage return}
          je    @14
          cmp   al, 13 {linefeed}
          je    @15

          inc   edi
          inc   dl
          cmp   dl, byte ptr [WindMax]
          jbe   @18
          call  @writedirect
          inc   dh
          cmp   dh, byte ptr [WindMax+1]
          jbe   @15
          dec   dh
          push  ecx
          push  edx
          mov   eax, $0601
          mov   bh, byte ptr [TextAttr]
          mov   cx, word ptr [WindMin]
          mov   dx, word ptr [WindMax]
          int   $10
          pop   edx
          pop   ecx

          mov   dl, byte ptr [WindMin]
          jmp   @17

      @12:
          call  @writedirect
          push   ecx
          push   edx
          mov    ax, $1407
          int    $10
          pop    edx
          pop    ecx
          jmp    @16
      @13:
          call  @writedirect
          cmp   dl, byte ptr [WindMin]
          je    @16
          dec   dl
          jmp   @16
      @14:
          call  @writedirect
          inc   dh
          cmp   dh, byte ptr [WindMax+1]
          jbe   @15
          dec   dh
          push  ecx
          push  edx
          mov   eax, $0601
          mov   bh, byte ptr [TextAttr]
          mov   cx, word ptr [WindMin]
          mov   dx, word ptr [WindMax]
          int   $10
          pop   edx
          pop   ecx
          jmp   @16
      @15:
          call  @writedirect
          mov   dl, byte ptr [WindMin]
      @16:
          inc   edi
      @17:
          mov   esi, edi
          mov   ebx, edx
      @18:
          dec   ecx
          jnz   @11

          call  @writedirect
          mov   word ptr fs:[$0400+$50], dx {cursor position}
          movzx ax, dh
          mul   byte ptr fs:[$0400+$4A]     {crt width}
          xor   dh, dh
          add   ax, dx
          movzx ecx, ax

          mov   dx, word ptr fs:[$0400+$63]  {address of video chip}
          mov   al, 14
          out   dx, al
          nop
          nop
          nop
          mov   al, ch
          inc   dx
          out   dx, al
          nop
          nop
          nop
          dec   dx
          mov   al, 15
          out   dx, al
          nop
          nop
          nop
          mov   al, cl
          inc   dx
          out   dx, al
          jmp   @exit

@writedirect:
{ BX = cursor position
  ESI = string start
  EDI = String end}
          movzx ebx, bx
          cmp   esi, edi
          je    @28

          push  ecx
          push  edx
          push  edi

          push  es

          push  fs
          pop   es

          mov   ecx, edi
          sub   ecx, esi

          movzx eax, bh
          mul   word ptr fs:[$400+$4A]     {crt width}
          xor   bh, bh
          add   eax, ebx
          shl   eax, 1
          mov   edi, eax

          mov   dx, word ptr fs:[$0400+$63]  {address of video chip}
          add   dx, 6
          cmp   word ptr fs:[$0400+$49], 7
          mov   eax, $0B8000
          jne   @21
          mov   eax, $0B0000
@21:
          mov   bl, byte ptr [CheckSnow]
          mov   bh, byte ptr [TextAttr]

          add   edi, eax
          cld   ;

          or    bl, bl
          je    @25
@22:                   {check for snow}
          lodsb ;
          mov   bl, al
@23:
          in    al, dx
          test  al, 1
          jne   @23
          cli   ;
@24:
          in    al, dx
          test  al, 1
          je    @24

          mov   eax, ebx
          stosw ;
          sti   ;
          loop  @22
          jmp   @27
@25:
          mov   ah, bh
@26:
          lodsb ;
          stosw ;
          loop  @26
@27:
          pop   es

          pop   edi
          pop   edx
          pop   ecx
@28:
          ret   ;
@exit:
  end;

procedure BiosWrite( Buf: Pointer; Count: LongInt); assembler;
  asm
          mov   ecx, dword ptr [Count]
          mov   edi, dword ptr [Buf]

        @@loop:
          mov   al, byte ptr [edi]

          push  ecx
          push  eax
          mov   ah, 3
          xor   bh, bh
          int   $10    {get cursor position}
          pop   eax

          cmp   al, 7  {bell}
          je    @1
          cmp   al, 8  {backspace}
          je    @2
          cmp   al, 13 {carriage return}
          je    @3
          cmp   al, 10 {linefeed}
          je    @4

          push  edx
          mov   ah, 9
          mov   bl, byte ptr [TextAttr]
          xor   bh, bh
          mov   cx, 1
          int   $10
          pop   edx

          inc   dl
          cmp   dl, byte ptr [WindMax]
          jbe   @5
          mov   dl, byte ptr [WindMin]
          jmp   @4

       @1:
          mov   ah, 14
          int   $10
          jmp   @5
       @2:
          cmp   dl, byte ptr [WindMin]
          je    @5
          dec   dl
          jmp   @5
       @3:
          mov   dl, byte ptr [WindMin]
          jmp   @5
       @4:              {do linefeed}
          inc   dh
          cmp   dh, byte ptr [WindMax+1]
          jbe   @5
          dec   dh
          push  edx
          mov   eax, $0601
          mov   bh, byte ptr [TextAttr]
          mov   cx, word ptr [WindMin]
          mov   dx, word ptr [WindMax]
          int   $10
          pop   edx
       @5:
          mov   ah, 2    {Set cursor position}
          xor   bh, bh
          int   $10

          pop   ecx
          inc   edi
          dec   ecx
          jnz   @@loop

  end;


const
  BreakState: Boolean = False;

procedure BreakCheck;
  begin
    if BreakState then Halt();
  end;

procedure CRT_Write( var TextFile: TextRec);
  begin
    if DirectVideo then
      DirectWrite( TextFile.BufPtr, TextFile.BufPos)
    else
      BiosWrite( TextFile.BufPtr, TextFile.BufPos);
    TextFile.BufPos := 0;
    BreakCheck();
  end;

procedure CRT_Read( var TextFile: TextRec); {assembler;}

  procedure InsChar( C: Char);
    begin
      if TextFile.BufEnd < TextFile.BufSize then
        begin
          TextFile.BufPtr^[ TextFile.BufEnd] := C;
          Inc( TextFile.BufEnd);
        end;
    end;

  const
    Carret: array[0..1] of Char = ( '^', ' ' );
    crlf: array[ 0..1] of Char = ( #13, #10 );
    DelChar: array [ 0..2] of Char = ( #8, #32, #8 );
  var
    c: Char;
  begin
    while True do
      begin
        ScanCode := #0;
        c := ReadKey();
        BreakCheck();
        case c of
          #13:
            begin
              BIOSWrite( @crlf, 2);
              InsChar( #13);
              InsChar( #10);
              break;
            end;
          #8:
            if TextFile.BufEnd > 0 then
              begin
                BIOSWrite( @DelChar, 3);
                Dec( TextFile.BufEnd);
              end;
          #27:
            while TextFile.BufEnd > 0 do
              begin
                BIOSWrite( @DelChar, 3);
                Dec( TextFile.BufEnd);
              end;
          #9:;
          #26:
            if CheckEOF then
              begin
                InsChar( #26);
                break;
              end;
          else
            if (c >= #32) and (TextFile.BufEnd < TextFile.BufSize) then
              begin
                BIOSWrite( @c, 1);
                InsChar( C);
              end;
        end;
      end;
    BreakCheck();
  end;

procedure CRT_Empty( var TextFile: TextRec);
  begin
  end;

procedure CRT_Open( var TextFile: TextRec);
  begin
    TextFile.CloseFunc := @CRT_Empty;
    TextFile.BufPtr := @TextFile.Buffer;
    TextFile.BufPos := 0;
    TextFile.BufEnd := 0;
    TextFile.BufSize := SizeOf( TextBuf);
    case TextFile.Mode of
      fmInput,
      fmInOut:
        begin
          TextFile.InOutFunc := @CRT_Read;
          TextFile.FlushFunc := @CRT_Empty;
        end;
      fmOutput:
        begin
          TextFile.InOutFunc := @CRT_Write;
          TextFile.FlushFunc := @CRT_Write;
        end;
    end;
  end;

procedure AssignCrt( var TextFile: Text);
  begin
    {TextRec( TextFile).Name := 'con';}
    TextRec( TextFile).Mode := fmClosed;
    TextRec( TextFile).OpenFunc := @CRT_Open;
  end;


procedure TextColor( Color: Byte); assembler;
  asm
    mov al, Color
    and al, $8F
    and TextAttr, $70
    or  TextAttr, al
  end;

procedure TextBackground( Color: Byte); assembler;
  asm
    mov al, Color
    and al, 7
    shl al, 4
    and TextAttr, $8F
    or  TextAttr, al
  end;

{
  DH = row
  DL = column
}
procedure SetCursor; assembler;
  asm
    mov ax, $0200
    xor bh, bh
    int $10
  end;

procedure GotoXY( X, Y: Byte); assembler;
  asm
    mov dl, x
    mov dh, y
    dec dl
    js  @@exit
    dec dh
    js  @@exit
    add dl, byte ptr [ WindMin]
    cmp dl, byte ptr [ WindMax]
    ja  @@exit
    add dh, byte ptr [ WindMin + 1]
    cmp dh, byte ptr [ WindMax + 1]
    ja  @@exit
    call SetCursor
  @@exit:
  end;

procedure Window( Left, Top, Right, Bottom: Byte); assembler;
  asm
    mov dl, Left
    mov dh, Top
    mov cl, Right
    mov ch, Bottom
    cmp dl, cl
    ja  @@exit
    cmp dh, ch
    ja  @@exit
    dec dl
    js  @@exit
    dec dh
    js  @@exit
    dec cl
    cmp cl, byte ptr [ CurScreenSize]
    ja  @@exit
    dec ch
    cmp ch, byte ptr [ CurScreenSize + 1]
    ja  @@exit
    mov WindMin, dx
    mov WindMax, cx
    call SetCursor
  @@exit:
  end;


procedure ClrScr; assembler;
  asm
    mov ax, $0600
    mov bh, TextAttr
    mov cx, WindMin
    mov dx, WindMax
    int $10
    mov dx, WindMin
    call SetCursor
  end;


procedure ClrEOL; assembler;
  asm
    mov ax, $0600
    mov bh, TextAttr
    mov cx, word ptr fs:[ $400 + $50] { get cursor position }
    mov dh, ch
    mov dl, byte ptr [ WindMax]
    int $10
  end;


procedure InsLine; assembler;
  asm
    mov ax, $0701
    mov bh, TextAttr
    mov ch, byte ptr fs:[ $0400 + $50 + 1]
    mov cl, byte ptr [ WindMin]
    mov dx, WindMax
    cmp ch, dh
    jne @@1
    xor al, al
  @@1:
    int $10
  end;

procedure DelLine; assembler;
  asm
    mov ax, $0601
    mov bh, TextAttr
    mov ch, byte ptr fs:[ $0400 + $50 + 1]
    mov cl, byte ptr [ WindMin]
    mov dx, WindMax
    cmp ch, dh
    jne @@1
    xor al, al
  @@1:
    int $10
  end;


function WhereX: Byte; assembler;
  asm
    mov   ah, 3
    xor   bh, bh
    int   $10
    sub   dl, byte ptr [WindMin]
    inc   dl
    movzx eax, dl
  end;

function WhereY: Byte; assembler;
  asm
    mov   ah, 3
    xor   bh, bh
    int   10h
    sub   dh, byte ptr [WindMin+1]
    inc   dh
    movzx eax, dh
  end;


procedure LowVideo; assembler;
  asm
    and TextAttr, $F7
  end;

procedure HighVideo; assembler;
  asm
    or TextAttr, 8
  end;

procedure NormVideo; assembler;
  asm
    mov al, NormAttr
    mov TextAttr, al
  end;

procedure Delay( ms: Word); assembler;
  asm
    mov ax, $8600
    xor ecx, ecx
    movzx edx, ms
    shl edx, 10
    shld ecx, edx, 16
    int $15
  end;

procedure Sound( Hz: Word); assembler;
  asm
    movzx ecx, Hz
    cmp ecx, 18
    jbe @@exit
    mov eax, $001234DD
    xor edx, edx
    div ecx
    mov ecx, eax
    mov al, 182
    out $43, al
    mov al, cl
    out $42, al
    mov al, ch
    out $42, al
    in  al, $61
    or  al, 3
    out $61, al
  @@exit:
  end;

procedure NoSound; assembler;
  asm
    in  al, $61
    and al, $FC
    out $61, al
  end;


type
  RealModeCallRegisters = record
    case integer of
      0: (EDI, ESI, EBP, L1, EBX, EDX, ECX, EAX: LongInt);
      1: (DI, W1, SI, W2, BP, W3, W4, W5, BX, W6, DX, W7, CX, W8, AX, W9,
          Flags, ES, DS, FS, GS, IP, CS, SP, SS: Word);
      2: (B1: array [0..15] of Byte;
          BL, BH, B2, B3, DL, DH, B4, B5, CL, CH, B6, B7, AL, AH: Byte);
  end;

var
  RealRegisters: RealModeCallRegisters;

begin
  asm
    mov ah, $0f
    int $10
    cmp al, 7
    je  @@1
    cmp al, 3
    jbe @@1
    mov al, 3
    push eax
    call SetCrtMode
  @@1:
    call SetCrtVariables
    mov ah, $08
    xor bh, bh
    int $10
    and ah, $7F
    mov NormAttr, ah
    mov TextAttr, ah
    xor al, al
    mov CheckEOF, al
    inc al
    mov CheckBreak, al
    
    jmp @@2

  @@Int1B:
      cld
      lodsw
      mov word ptr es:[edi].RealModeCallRegisters.&IP, ax
      lodsw
      mov word ptr es:[edi].RealModeCallRegisters.&CS, ax
      lodsw
      mov word ptr es:[edi].RealModeCallRegisters.&FLAGS, ax
      add word ptr es:[edi].RealModeCallRegisters.&SP, 6
      cmp es:[CheckBreak], 0
      jz  @@Int1B@exit
      mov es:[BreakState], 1

    @@Int1B@exit:
      iret

  @@2:

      mov esi, offset @@int1b
      mov edi, offset RealRegisters
      push ds
      push cs
      pop ds
      mov eax, $0303
      int $31
      mov eax, $0201
      mov bl, $1B
      int $31
      pop ds
    
  end;
  AssignCrt( OutPut); ReWrite( OutPut);
  AssignCrt( InPut); ReSet( InPut);
end.