{                    GNU GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Full text of license:
 https://www.gnu.org/licenses/gpl-3.0.en.html

 (c) Copyright 2022 DosWord
 (c) Copyright 1997-1998 Iggor Khachko - hachko@icl.kazan.su }

{$IFDEF TP}
{$X+,V-,G+,N+,E-,B-,T-}

{$IFDEF DEBUG}
{$I+,S+,R+,C+}
{$ELSE}
{$I-,S-,R-,C-}
{$ENDIF}

{$ENDIF}

unit StdLib;

interface

uses Dos;

function FExists( const FileName: PathStr): Boolean;
function ReplaceExt(FileName: PathStr; NExt: ExtStr; Force: Boolean):
  PathStr;
function ReplaceName(FileName:PathStr;NewName:String): PathStr;
function UpperCase(C: Char): Char;
function UpStr(Str: String): String;
function LoCase(C: Char): Char;
function LoStr(Str: String): String;
function Ext(FileName: PathStr): ExtStr;
function LTrim(S: String): String;
function RTrim(S: String): String;

procedure CreateTempFile(var Path: PathStr);
procedure EraseFile(const FN: PathStr);
function GetFileTime( const FileName: String): LongInt;

function GetRelativePath( const FileName: String): String;

function ToStr( L: LongInt): String;

procedure ClrLine;

procedure WriteString( const S: String);

function ExtractFileName( const Path: PathStr): NameStr;
function ExtractDirectory( const Path: PathStr): DirStr;
function ExtractExtension( const Path: PathStr): ExtStr;

const
  _EOL_:String[2] = #13#10;

implementation


function ToStr( L: LongInt): String;
  var
    S: String[12];
  begin
    Str(L, S);
    ToStr := S;
  end;

function FExists( const FileName: PathStr): Boolean;
var
  F: file;
  Attr: Word;
begin
  Assign(F, FileName);
  GetFAttr(F, Attr);
  FExists := DosError = 0;
end;

function ReplaceExt(FileName: PathStr; NExt: ExtStr; Force: Boolean):
  PathStr;
var
  Dir: DirStr;
  Name: NameStr;
  Ext: ExtStr;
begin
  FileName := UpStr(FileName);
  FSplit(FileName, Dir, Name, Ext);
  if Force or (Ext = '') then
    ReplaceExt := Dir + Name + NExt else
    ReplaceExt := FileName;
end;

function Ext(FileName: PathStr): ExtStr;
var
  Dir: DirStr;
  Name: NameStr;
  E: ExtStr;
begin
  FileName := UpStr(FileName);
  FSplit(FileName, Dir, Name, E);
  Ext := E
end;

function UpperCase(C: Char): Char; Assembler;
  asm
    mov al,c
    cmp al,'a'
    jb  @@1
    cmp al,'a'
    ja @@1
    xor al,$20
    jmp @@4
   @@1:
    cmp al,'†'
    jb @@2
    cmp al,'Ø'
    ja @@2
    xor al,$20
    jmp @@4
   @@2:
    cmp al,'‡'
    jb @@3
    cmp al,'Ô'
    ja @@3
    add al,80
    jmp @@4
   @@3:
    cmp al,'Ò'
    jne @@4
    mov al,''
   @@4:
  end;

function ReplaceName(FileName:PathStr;NewName:String): PathStr;
  var
    Dir: DirStr;
    Name: NameStr;
    Ext: ExtStr;
  begin
    FileName := UpStr(FileName);
    FSplit(FileName, Dir, Name, Ext);
    ReplaceName := Dir + NewName;
  end;

function UpStr(Str: String): String;
var
  I: Integer;
begin
  for I := 1 to Length(Str) do
    Str[I] := UpCase(Str[I]);
  UpStr := Str;
end;

function LoCase(C: Char): Char; Assembler;
  asm
    mov al,c
    cmp al,'A'
    jb  @@1
    cmp al,'Z'
    ja @@1
    xor al,$20
    jmp @@4
   @@1:
    cmp al,'Ä'
    jb @@2
    cmp al,'è'
    ja @@2
    xor al,$20
    jmp @@4
   @@2:
    cmp al,'ê'
    jb @@3
    cmp al,'ü'
    ja @@3
    add al,80
    jmp @@4
   @@3:
    cmp al,''
    jne @@4
    mov al,'Ò'
   @@4:
  end;

function LoStr(Str: String): String;
var
  I: Integer;
begin
  for I := 1 to Length(Str) do
    Str[I] := LoCase(Str[I]);
  LoStr := Str;
end;

procedure CreateTempFile(var Path: PathStr); Assembler;
  asm
{$IFDEF TP}
    push DS
    lds si,Path
    lodsb
    mov bl,al
    xor bh,bh
    mov byte ptr ds:[si+bx],0
    mov dx,si
    mov ax,5A00h
    mov cx,0
    int 21h

{    mov bx,ax
    mov ah,3eh
    int 21h}

    mov di,dx
    mov ax,ds
    mov es,ax
    jnc @@1
    mov byte ptr es:[di],0
  @@1:
    xor al,al
    mov cx,$FF
    repne scasb
    mov al,$FF
    sub al,cl
    mov di,dx
    dec di
    mov es:[di],al
    pop  DS
{$ENDIF}
{$IFDEF PPRO}
    mov esi, dword ptr [ Path]
    lodsb
    movzx ebx, al
    mov byte ptr [esi+ebx],0
    mov edx, esi
    mov eax,$5A00
    mov ecx,0
    int $21

{    mov bx,ax
    mov ah,3eh
    int 21h}

    mov edi, edx
    jnc @@1
    mov byte ptr [edi],0
  @@1:
    xor al,al
    mov cx,$FF
    repne scasb
    mov al,$FF
    sub al,cl
    mov edi, edx
    dec edi
    mov byte ptr [edi],al
{$ENDIF}
  end;

procedure EraseFile(const FN: PathStr); Assembler;
  asm
{$IFDEF TP}
    push DS
    lds si,FN
    lodsb
    mov bl,al
    xor bh,bh
    mov byte ptr ds:[si+bx],0
    mov dx,si
    mov ax,4100h
    mov cx,0
    int 21h
    pop DS
{$ENDIF}
{$IFDEF PPRO}
    mov edi, dword ptr [ FN]
    lodsb
    movzx ebx, al
    mov byte ptr [esi+ebx],0
    mov edx,esi
    mov eax, $4100
    mov ecx,0
    int $21
{$ENDIF}
  end;

function LTrim(S: String): String;
  begin
    if S<> '' then
      while S[1] = ' ' do S := Copy(S, 2, Byte(S[0]) - 1);
    LTrim := S;
  end;

function RTrim(S: String): String;
  begin
    if S<>'' then
      while S[Byte(S[0])] = ' ' do Dec(S[0]);
    RTrim := S;
  end;


function GetFileTime( const FileName: String): LongInt;
  var
    F: File;
    L: LongInt;
  begin
    Assign( F, FileName);
{$IFDEF TP}
    {$I-}
{$ENDIF}
    Reset( F);
{$IFDEF TP}
    if IoResult <> 0 then
{$ENDIF}
{$IFDEF PPRO}
    if IoResult() <> 0 then
{$ENDIF}
      L := 0
    else
      begin
        GetFTime( F, L);
        Close( F);
      end;
    GetFileTime := L;
  end;


function GetRelativePath( const FileName: String): String;
  var
    CurDir, FName, Res: String;
    I: Integer;
  begin
    GetDir( 0, CurDir);
    if CurDir[ Length( CurDir)] <> '\' then
      CurDir := CurDir + '\';
    FName := FExpand( FileName);
    if (Length( CurDir) <= 1) or (Length( FName) <= 1) or
      (CurDir[1] <> FName[1]) then
      GetRelativePath := FName
    else
      begin
        Res := '';
        while (Length( CurDir) > 0) and (Length( FName)> 0) and
          (CurDir[1] = FName[1]) do
          begin
            Delete( CurDir, 1, 1);
            Delete( FName, 1, 1);
          end;
        I := Pos( '\', FName);
        while I > 0 do
          begin
            Res := Res + '..\';
            Delete( FName, 1, I);
            I := Pos( '\', FName);
          end;
        Res := Res + CurDir;
        {if Res[ Length(Result)] <> '\' then
          Res := Res + '\';}
        GetRelativePath := Res + FName;
      end;
  end;


procedure WriteString( const S: String); assembler;
  asm
    {$IFDEF PPRO}
        mov esi, dword ptr [ S]
        cld
        lodsb
        movzx ecx, al
        mov eax, $40
        mov ebx, 1
        mov edx, esi
        int $21
    {$ELSE}
        push ds
        lds si, s
        cld
        lodsb
        xor ah, ah
        xchg ax, cx
        mov ah, 40h
        mov bx, 1
        mov dx, si
        int 21h
        pop ds
    {$ENDIF}
  end;

procedure ClrLine;
  begin
    Write( #13'                                                                               '#13);
  end;

function ExtractFileName( const Path: PathStr): NameStr;
  var
    D: DirStr;
    N: NameStr;
    E: ExtStr;
  begin
    FSplit( Path, D, N, E);
    ExtractFileName := N;
  end;

function ExtractDirectory( const Path: PathStr): DirStr;
  var
    D: DirStr;
    N: NameStr;
    E: ExtStr;
  begin
    FSplit( Path, D, N, E);
    ExtractDirectory := D;
  end;

function ExtractExtension( const Path: PathStr): ExtStr;
  var
    D: DirStr;
    N: NameStr;
    E: ExtStr;
  begin
    FSplit( Path, D, N, E);
    ExtractExtension := E;
  end;


end.
