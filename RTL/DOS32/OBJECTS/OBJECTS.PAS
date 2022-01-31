{                    GNU LESSER GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Full text of license:
 https://www.gnu.org/licenses/lgpl-3.0.en.html

 (c) Copyright 2022 DosWord
 (c) Copyright 1997-1998 Iggor Khachko - hachko@icl.kazan.su }

unit Objects;

{$IFNDEF PPRO}
{$ERROR Pascal Pro compiler required.}
{$ENDIF}

{$IFNDEF DOS32}
{$ERROR Must be DOS32 target}
{$ENDIF}

interface

const

{ TStream access modes }

  stCreate    = $3C00;           { Create new file }
  stOpenRead  = $3D00;           { Read access only }
  stOpenWrite = $3D01;           { Write access only }
  stOpen      = $3D02;           { Read and write access }

{ tStream error codes }

const

  stOK         =  0;              { No error }
  stError      = -1;              { Access error }
  stInitError  = -2;              { Stream initialization error }
  stReadError  = -3;              { Error reading from a stream }
  stWriteError = -4;              { Error writing to a stream }
  stGetError   = -5;              { Get of unregistered object type }
  stPutError   = -6;              { Put of unregistered object type }

{ tCollection error codes }

  coIndexError          = -1;   { Index our of range }
  coOverflow            = -2;   { Overflow }

{ VMT header size }
  vmtHeaderSize         = 12;
  NearPointerSize       = 4;

type

  pString = ^String;

{$IFDEF PPRO}
  tIndex = LongInt;
  tSize = LongInt;
{$ELSE}
  tIndex = Word;
  tSize = Word;
{$ENDIF}

const
{ Maximum tCollection size }
  MaxCollectionSize = High( tIndex) div SizeOf( Pointer);

type
  WordRec = record
    Lo, Hi: Byte;
  end;

  LongRec = record
    Lo, Hi: Word;
  end;

{ Character set type }

  PCharSet = ^TCharSet;
  TCharSet = set of Char;

{ General arrays }

  PByteArray = ^TByteArray;
  TByteArray = array[0..High( tIndex)] of Byte;

  PWordArray = ^TWordArray;
  TWordArray = array[0..High( tIndex) shr 1] of Word;

type

  { tObject is a root for all objects in this unit }
  pObject = ^tObject;
  tObject = object
    public
      constructor Init;
      destructor Done; virtual;
      procedure Free;
  end;

type
    { tStreamRec }
  pStreamRec = ^tStreamRec;
  tStreamRec = record
    ObjType: LongInt;
    VmtLink: Pointer;
    Load: Pointer;
    Store: Pointer;
    Next: pStreamRec;
  end;

type
  { tStream is an abstract stream }
  pStream = ^tStream;
  tStream = object( tObject)
    public
      Status: Integer;
      ErrorInfo: Integer;
      
      constructor Init;

        { Copies Count bytes from S }
      procedure CopyFrom( var S: tStream; Count: tSize);

        { Called whenever error occured }
      procedure Error( Code, Info: LongInt); virtual;
        { Clears error stream status }
      procedure Reset;

        { Reads Count bytes from stream to Buf }
      procedure Read( var Buf; Count: tSize); virtual;
        { Writes Count bytes from Buf to stream }
      procedure Write( var Buf; Count: tSize); virtual;
        { Clears any buffers }
      procedure Flush; virtual;
        { Reads string from stream }
      function ReadStr: pString;
        { Writes string to stream }
      procedure WriteStr( P: pString);
        { Reads ASCIIZ string from stream }
      function StrRead: pChar;
        { Writes ASCIIZ string to stream }
      procedure StrWrite( P: pChar);

        { Reads an object from stream (object must be a descendant of tObject) }
      function Get: pObject;
        { Writes an object to stream (object must be a descendant of tObject) }
      procedure Put( P: pObject);

        { Returns current position in a stream (relative beginning) }
      function GetPos: tSize; virtual;
        { Returns size of stream }
      function GetSize: tSize; virtual;

        { Sets the current position to Pos from start of stream }
      procedure Seek( Pos: tSize); virtual;
        { Deletes all data in a stream from current position to the end }
      procedure Truncate; virtual;
  end;

type
  FNameStr = String[ 79];

type
  { tDosStream }
  pDosStream = ^tDosStream;
  tDosStream = object( tStream)
    public
      Handle: Word;

      constructor Init( const FileName: FNameStr; Mode: Word);
      destructor Done; virtual;

      procedure Read(var Buf; Count: tSize); virtual;
      procedure Write(var Buf; Count: tSize); virtual;

      function GetPos: tSize; virtual;
      function GetSize: tSize; virtual;
      procedure Seek(Pos: tSize); virtual;
      procedure Truncate; virtual;
  end;

type
  pBufStream = ^tBufStream;
  tBufStream = object( tDosStream)
    public
      Buffer: Pointer;
      BufSize: tSize;
      BufPtr: tSize;
      BufEnd: tSize;

      constructor Init( const FileName: FNameStr; Mode: Word; Size: tSize);
      destructor Done; virtual;

      procedure Read( var Buf; Count: tSize); virtual;
      procedure Write( var Buf; Count: tSize); virtual;
      procedure Flush; virtual;

      function GetPos: tSize; virtual;
      function GetSize: tSize; virtual;
      procedure Seek( Pos: tSize); virtual;
      procedure Truncate; virtual;
  end;

type

    { tCollection types }
  pItemList = ^tItemList;
  tItemList = array [0..MaxCollectionSize - 1] of Pointer;

    { tCollection }
  pCollection = ^tCollection;
  tCollection = object( tObject)
    public
      Items: pItemList;
      Count: tIndex;
      Limit: tIndex;
      Delta: tIndex;

      constructor Init( aLimit, aDelta: tIndex);
      destructor Done; virtual;
      constructor Load( var S: tStream);
      procedure Store( var S: tStream);

      function At( Index: tIndex): Pointer;
      procedure AtDelete( Index: tIndex);
      procedure AtFree( Index: tIndex);
      procedure AtInsert( Index: tIndex; Item: Pointer);
      procedure AtPut( Index: tIndex; Item: Pointer);
      procedure Delete( Item: Pointer);
      procedure DeleteAll;
      procedure Error( Code, Info: Integer); virtual;
      function FirstThat( Test: Pointer): Pointer;
      procedure ForEach( Action: Pointer);
      procedure Free( Item: Pointer);
      procedure FreeAll;
      procedure FreeItem( Item: Pointer); virtual;
      function GetItem( var S: tStream): Pointer; virtual;
      function IndexOf( Item: Pointer): tIndex; virtual;
      procedure Insert( Item: Pointer); virtual;
      function LastThat( Test: Pointer): Pointer;
      procedure Pack;
      procedure PutItem( var S: tStream; Item: Pointer); virtual;
      procedure SetLimit( aLimit: tIndex); virtual;
  end;


{ tSortedCollection }
type
  pSortedCollection = ^tSortedCollection;
  tSortedCollection = object( tCollection)
    public
      Duplicates: Boolean;

      constructor Init( aLimit, aDelta: tIndex);
      constructor Load( var S: tStream);
      procedure Store( var S: tStream);

      function Compare( Key1, Key2: Pointer): LongInt; virtual;
      function IndexOf( Item: Pointer): tIndex; virtual;
      procedure Insert( Item: Pointer); virtual;
      function KeyOf( Item: Pointer): Pointer; virtual;
      function Search( Key: Pointer; var Index: tIndex): Boolean; virtual;
  end;


{ tStringCollection }
type
  pStringCollection = ^tStringCollection;
  tStringCollection = object( tSortedCollection)
    public
      function Compare( Key1, Key2: Pointer): LongInt; virtual;
      function GetItem( var S: tStream): Pointer; virtual;
      procedure PutItem( var S: tStream; Item: Pointer); virtual;
      procedure FreeItem( Item: Pointer); virtual;
  end;

{ tStrCollection }
type
  pStrCollection = ^tStringCollection;
  tStrCollection = object( tSortedCollection)
    public
      function Compare( Key1, Key2: Pointer): LongInt; virtual;
      function GetItem( var S: tStream): Pointer; virtual;
      procedure PutItem( var S: tStream; Item: Pointer); virtual;
      procedure FreeItem( Item: Pointer); virtual;
  end;

type
  tStreamErrorProc = procedure( var S: tStream);

const
    { Stream error handler }
  StreamErrorHandler: tStreamErrorProc = nil;


  { Abstract notification procedure }
procedure Abstract;

  { Type registration routine }
procedure RegisterType( var S: tStreamRec);

procedure RegisterObjects;

  { pString routines }
function NewStr( const Val: String): pString;
procedure DisposeStr( P: pString);

const
  RCollection: tStreamRec = (
    ObjType: 50;
    VmtLink: TypeOf( tCollection);
    Load: @tCollection.Load;
    Store: @tCollection.Store;
  );

  RStringCollection: tStreamRec = (
    ObjType: 51;
    VmtLink: TypeOf( tStringCollection);
    Load: @tStringCollection.Load;
    Store: @tStringCollection.Store;
  );

  RStrCollection: tStreamRec = (
    ObjType: 52;
    VmtLink: TypeOf( tStrCollection);
    Load: @tStrCollection.Load;
    Store: @tStrCollection.Store;
  );

implementation

uses Strings;

const
  tStream_Error         = vmtHeaderSize + NearPointerSize * ( 2 - 1 );
  tStream_Read          = vmtHeaderSize + NearPointerSize * ( 3 - 1 );
  tStream_Write         = vmtHeaderSize + NearPointerSize * ( 4 - 1 );

const
  StreamTypes: pStreamRec = nil;

{ DoStreamError calls tStream.Error
  In:
    DX = Status
    AX = ErrorInfo
    EDI = Self }

procedure DoStreamError; assembler;
  asm
    push edi
    push edx
    push eax
    mov ebx, dword ptr [ edi]
    call dword ptr [ebx + tStream_Error]
  end;

{ tObject }
constructor tObject.Init; assembler;
  asm
    mov edi, dword ptr [Self]
    mov ebx, dword ptr [edi]
    mov ecx, dword ptr [ebx]
    sub ecx, 4
    jz  @@Exit
    xor eax, eax
    add edi, 4
    rep stosb

  @@Exit:
  end;

destructor tObject.Done;
  begin
  end;

procedure tObject.Free;
  var
    P: pObject;
  begin
    P := @Self;
    Dispose( P, Done() );
  end;


{ tStream }

constructor tStream.Init;
  begin
    inherited Init();
    Status := stOK;
    ErrorInfo := 0;
  end;

procedure tStream.CopyFrom( var S: tStream; Count: tSize);
  var
    N: tSize;
    Buf: array [0..1023] of Byte;
  begin
    while Count > 0 do
      begin
        if Count > 1024 then
          N := SizeOf( Buf)
        else
          N := Count;
        S.Read( Buf, N);
        Write( Buf, N);
        Dec( Count, N);
      end;
  end;

procedure tStream.Error( Code, Info: LongInt);
  begin
    Status := Code;
    ErrorInfo := Info;
    if Assigned( StreamErrorHandler) then
      StreamErrorHandler( Self);
  end;

procedure tStream.Reset;
  begin
    Status := stOK;
    ErrorInfo := 0;
  end;

procedure tStream.Read( var Buf; Count: tSize);
  begin
    Abstract();
  end;

procedure tStream.Write( var Buf; Count: tSize);
  begin
    Abstract();
  end;

procedure tStream.Flush;
  begin
  end;

function tStream.ReadStr: pString;
  var
    C: Char;
  begin
    Read( C, SizeOf( Char));
    GetMem( ReadStr, Ord( C) + 1);
    Read( ReadStr^[ 1], Ord( C));
    ReadStr^[ 0] := C;
  end;

procedure tStream.WriteStr( P: pString);
  const
    C: Char = #0;
  begin
    if not Assigned( P) then
      Write( C, SizeOf( C))
    else
      Write( P^, Length( P^) + 1);
  end;

function tStream.StrRead: pChar;
  var
    L: LongInt;
  begin
    Read( L, SizeOf( L));
    if L >0 then
      begin
        GetMem( Result, L + 1);
        Read( Result[ 0], L);
        Result[ L] := #0;
      end
    else
      Result := nil;  
  end;

procedure tStream.StrWrite( P: pChar);
  var
    L: LongInt;
  begin
    L := StrLen( P);
    Write( L, SizeOf( L));
    if Assigned( P) then
      Write( P[ 0], L);
  end;

function tStream.Get: pObject; assembler;
  var
    ObjType: LongInt;
  asm
    lea eax, ObjType
    mov edi, dword ptr [ Self]
    mov ebx, dword ptr [ edi]
    push edi
    push eax
    push 4
    call dword ptr [ ebx + tStream_Read]

    mov eax, ObjType
    or  eax, eax
    je  @@Exit

    mov esi, StreamTypes

  @@1:
    or  esi, esi
    je  @@Error
    cmp [ esi].tStreamRec.ObjType, eax
    je  @@Read
    mov esi, [ esi].tStreamRec.Next
    jmp @@1

  @@Error:
    mov edx, stGetError
    xor eax, eax
    mov edi, dword ptr [ Self]
    call DoStreamError
    jmp @@Exit

  @@Read:
    mov ebx, [ esi].tStreamRec.VmtLink
    push esi
    push ebx

    lea eax, ObjType
    push eax
    mov eax, dword ptr [ ebx]
    push eax
    call GetMem

    pop ebx
    pop esi
    mov eax, ObjType
    or  eax, eax
    je  @@Exit
    mov dword ptr [ eax], ebx

    push eax
    mov eax, dword ptr [ Self]
    push eax

    call [ esi].tStreamRec.Load
    mov eax, [ ObjType]

  @@Exit:
  end;

procedure tStream.Put( P: pObject); assembler;
  asm
    xor ecx, ecx
    mov esi, ecx
    mov edi, P
    or  edi, edi
    je  @@Write
    mov eax, dword ptr [ edi]  { VMT }
    mov esi, StreamTypes

  @@1:
    or  esi, esi
    je  @@DoError
    mov ecx, [esi].tStreamRec.ObjType
    cmp eax, [esi].tStreamRec.VmtLink
    je  @@Write
    mov esi, [esi].tStreamRec.Next
    jmp @@1

  @@Write:
    push esi
    mov edi, dword ptr [ Self]
    mov ebx, dword ptr [ edi]
    push ecx
    mov  eax, esp
    push edi
    push eax
    push 4
    call dword ptr [ ebx + tStream_Write]

    pop ecx
    pop esi
    or  esi, esi
    je  @@Exit

    mov eax, P
    push eax
    mov edi, dword ptr [ Self]
    push edi
    call [ esi].tStreamRec.Store
    jmp @@Exit

  @@DoError:
    mov edx, stPutError
    xor eax, eax
    mov edi, dword ptr [ Self]
    call DoStreamError

  @@Exit:
  end;

function tStream.GetPos: tSize;
  begin
    Abstract();
  end;

function tStream.GetSize: tSize;
  begin
    Abstract();
  end;

procedure tStream.Seek( Pos: tSize);
  begin
    Abstract();
  end;

procedure tStream.Truncate;
  begin
    Abstract();
  end;


{ tDosStream }

constructor tDosStream.Init( const FileName: FNameStr; Mode: Word); assembler;
  var
    Buf: array [ 0..79] of Byte;
  asm
    mov eax, dword ptr [ Self]
    push eax
    call tStream.Init

    mov esi, dword ptr [ FileName]
    lea edi, Buf
    mov edx, edi
    cld
    lodsb
    cmp al, 79
    jbe @@1
    mov al, 79
  @@1:
    movzx ecx, al
    jcxz @@2
    rep movsb
  @@2:
    xor al, al
    stosb
    movzx eax, Mode
    xor ecx, ecx
    int $21
    jnc @@Exit

    mov dx, stInitError
    mov edi, dword ptr [ Self]
    call DoStreamError
    mov ax, -1

  @@Exit:
    mov edi, dword ptr [ Self]
    mov [ edi].tDosStream.Handle, ax
  end;

destructor tDosStream.Done; assembler;
  asm
    mov edi, dword ptr [ Self]
    push edi
    mov bx, [ edi].tDosStream.Handle
    cmp bx, -1
    je @@1
    mov eax, $3E00
    int $21
  @@1:
    call tStream.Done
  end;

procedure tDosStream.Read(var Buf; Count: tSize); assembler;
  asm
    mov edi, dword ptr [ Self]
    mov ax, [ edi].tDosStream.Status
    or  ax, ax
    jne @@1
    mov bx, [ edi].tDosStream.Handle
    cmp bx, -1
    je  @@Error
    mov eax, $3F00
    mov ecx, Count
    mov edx, dword ptr [ Buf]
    int $21
    mov dx, stError
    jc  @@Error
    cmp eax, Count
    je  @@Exit
    xor eax, eax
    mov dx, stReadError

  @@Error:
    mov edi, dword ptr [ Self]
    call DoStreamError
  @@1:
    mov edi, dword ptr [ Buf]
    mov ecx, Count
    jcxz @@Exit
    xor al, al
    cld
    rep stosb

  @@Exit:
  end;

procedure tDosStream.Write(var Buf; Count: tSize); assembler;
  asm
    mov edi, dword ptr [ Self]
    mov ax, [ edi].tDosStream.Status
    or  ax, ax
    jne @@Exit
    mov bx, [ edi].tDosStream.Handle
    cmp bx, -1
    je  @@Error
    mov eax, $4000
    mov ecx, Count
    mov edx, dword ptr [ Buf]
    int $21
    mov dx, stError
    jc  @@Error
    cmp eax, Count
    je  @@Exit
    xor eax, eax
    mov dx, stWriteError

  @@Error:
    mov edi, dword ptr [ Self]
    call DoStreamError

  @@Exit:
  end;

function tDosStream.GetPos: tSize; assembler;
  asm
    mov edi, dword ptr [ Self]
    cmp [edi].tDosStream.Status, 0
    jne @@1
    xor edx, edx
    mov bx,[edi].tDosStream.Handle
    mov ax,$4201
    int $21
    jnc @@Exit
    mov edx, stError
    mov edi, dword ptr [ Self]
    call DoStreamError
  @@1:
    mov eax, -1
  @@Exit:
  end;

function tDosStream.GetSize: tSize; assembler;
  asm
    mov edi, dword ptr [ Self]
    cmp [edi].tDosStream.Status, 0
    jne @@1
    xor edx, edx
    mov bx,[edi].tDosStream.Handle
    mov ax,$4201
    int $21
    push eax
    mov ax, $4202
    xor edx, edx
    int $21
    pop edx
    push eax
    mov ax, $4200
    int $21
    pop eax
    jnc @@Exit
    mov edx, stError
    mov edi, dword ptr [ Self]
    call DoStreamError
  @@1:
    mov eax, -1
  @@Exit:
  end;

procedure tDosStream.Seek(Pos: tSize); assembler;
  asm
    mov edi, dword ptr [ Self]
    cmp [edi].tDosStream.Status, 0
    jne @@Exit
    mov bx,[edi].tDosStream.Handle
    mov eax, $4200
    mov edx, dword ptr [ Pos]
    or  edx, edx
    jns @@1
    xor edx, edx
  @@1:
    int $21
    jnc @@Exit
    mov edx, stError
    mov edi, dword ptr [ Self]
    call DoStreamError
  @@Exit:
  end;

procedure tDosStream.Truncate; assembler;
  asm
    mov edi, dword ptr [ Self]
    cmp [edi].tDosStream.Status, 0
    jne @@Exit
    mov bx, [edi].tDosStream.Handle
    mov eax, $4000
    xor ecx, ecx
    int $21
    jnc @@Exit
    mov edx, stError
    mov edi, dword ptr [ Self]
    call DoStreamError
  @@Exit:
  end;


  { tBufStream }
constructor tBufStream.Init( const FileName: FNameStr; Mode: Word; Size: tSize);
  begin
    inherited Init( FileName, Mode);
    BufSize := Size;
    if Size > 0 then
      GetMem( Buffer, Size)
    else
      Error( stInitError, 0);
    BufPtr := 0;
    BufEnd := 0;
  end;

destructor tBufStream.Done;
  begin
    Flush();
    inherited Done();
    FreeMem( Buffer, BufSize);
  end;

{
  In:
    EDI = Self
    AL = FlushMode ( 0 = Read , 1 = Write , 2 = Read & Write 
  Out:
    ZF = Status test
}
procedure FlushBuffer; assembler;
  asm
    movzx ebx, [ edi].tBufStream.Handle
    mov edx, [ edi].tBufStream.BufPtr
    sub edx, [ edi].tBufStream.BufEnd
    je  @@OK
    jg  @@Write
    cmp al, 1
    je  @@Exit
    mov eax, $4201
    int $21
    jmp @@OK

  @@Write:
    or  al, al
    je  @@Exit
    mov edx, [ edi].tBufStream.Buffer
    mov eax, $4000
    int $21
    mov edx, stError
    jc  @@DoError
    cmp eax, ecx
    je  @@OK
    xor eax, eax
    mov edx, stWriteError
  @@DoError:
    call DoStreamError

  @@OK:
    xor eax, eax
    mov [ edi].tBufStream.BufPtr, eax
    mov [ edi].tBufStream.BufEnd, eax
    cmp ax, [ edi].tBufStream.Status
  @@Exit:
  end;

procedure tBufStream.Read( var Buf; Count: tSize); assembler;
  asm
    mov edi, dword ptr [ Self]
    cmp [ edi].tBufStream.Status, 0
    jne @@ZFill
    mov al, 1
    call FlushBuffer
    jne @@ZFill
    xor ebx, ebx

  @@ReadLoop:
    mov ecx, Count
    sub ecx, ebx
    je  @@Exit
    mov edi, dword ptr [ Self]
    mov eax, [ edi].tBufStream.BufEnd
    sub eax, [ edi].tBufStream.BufPtr
    jg  @@1
    push ebx
    push ecx
    mov eax, $3F00
    mov bx, [ edi].tBufStream.Handle
    mov edx, [ edi].tBufStream.Buffer
    mov ecx, [ edi].tBufStream.BufSize
    int $21
    pop ecx
    pop ebx
    mov edx, stError
    jc  @@DoError
    mov [ edi].tBufStream.BufPtr, 0
    mov [ edi].tBufStream.BufEnd, eax
    or  eax, eax
    je  @@Error
  @@1:
    cmp ecx, eax
    jle @@2
    mov ecx, eax
  @@2:
    mov esi, [ edi].tBufStream.Buffer
    add esi, [ edi].tBufStream.BufPtr
    add [ edi].tBufStream.BufPtr, ecx
    mov edi, dword ptr [ Buf]
    add edi, ebx
    add ebx, ecx
    cld
    rep movsb
    jmp @@ReadLoop

  @@Error:
    mov edx, stReadError
  @@DoError:
    mov edi, dword ptr [ Self]
    call DoStreamError

  @@ZFill:
    mov edi, dword ptr [ Self]
    mov ecx, Count
    jcxz @@Exit
    xor al, al
    cld
    rep stosb

  @@Exit:
  end;

procedure tBufStream.Write( var Buf; Count: tSize); assembler;
  asm
    mov edi, dword ptr [ Self]
    cmp [ edi].tBufStream.Status, 0
    jne @@Exit
    xor al, al
    call FlushBuffer
    jne @@Exit
    xor edx, edx

  @@WriteLoop:
    mov ecx, Count
    mov edi, dword ptr [ Self]
    sub ecx, edx
    je  @@Exit
    mov eax, [ edi].tBufStream.BufSize
    sub eax, [ edi].tBufStream.BufPtr
    jg  @@1
    push ecx
    push edx
    mov al, 1
    call FlushBuffer
    pop edx
    pop eax
    jne @@Exit
    mov eax, [ edi].tBufStream.BufSize
  @@1:
    cmp ecx, eax
    jle @@2
    mov ecx, eax
  @@2:
    mov esi, dword ptr [ Buf]
    add esi, edx
    add edx, ecx
    mov eax, [ edi].tBufStream.Buffer
    add eax, [ edi].tBufStream.BufPtr
    add [ edi].tBufStream.BufPtr, ecx
    mov edi, eax
    cld
    rep movsb
    jmp @@WriteLoop

  @@Exit:
  end;

procedure tBufStream.Flush; assembler;
  asm
    mov edi, dword ptr [ Self]
    cmp [ edi].tBufStream.Status, 0
    jne @@Exit
    mov al, 2
    call FlushBuffer
  @@Exit:
  end;

function tBufStream.GetPos: tSize; assembler;
  asm
    mov edi, dword ptr [ Self]
    push edi
    call tDosStream.GetPos
    or  eax, eax
    js  @@Exit
    mov edi, dword ptr [ Self]
    sub eax, [ edi].tBufStream.BufEnd
    add eax, [ edi].tBufStream.BufPtr
  @@Exit:
  end;

function tBufStream.GetSize: tSize; assembler;
  asm
    mov edi, dword ptr [ Self]
    push edi
    mov al, 2
    call FLushBuffer
    call tDosStream.GetSize
  end;

procedure tBufStream.Seek( Pos: tSize); assembler;
  asm
    push dword ptr [ Self]
    push Pos
    call tDosStream.GetPos
    mov edi, dword ptr [ Self]
    sub eax, Pos
    jl  @@1
    mov edx, [ edi].tBufStream.BufEnd
    sub edx, eax
    jl  @@1
    cmp edx, [ edi].tBufStream.BufPtr
    jl  @@1
    mov [ edi].tBufStream.BufPtr, edx
    jmp @@Exit

  @@1:
    push edi
    push Pos
    mov al, 2
    call FlushBuffer
    call tDosStream.Seek

  @@Exit:
  end;

procedure tBufStream.Truncate; assembler;
  asm
    mov edi, dword ptr [ Self]
    push edi
    mov al, 2
    call FLushBuffer
    call tDosStream.Truncate
  end;


{ tCollection }

const
  tCollection_Error    = vmtHeaderSize + NearPointerSize * ( 2 - 1 );
  tCollection_SetLimit = vmtHeaderSize + NearPointerSize * ( 8 - 1 );

{
  In
    edi = Object pointer
    eax = Error code
    ebx = Error info
}
procedure CollectionError; assembler;
  asm
    push edi
    push eax
    push ebx
    mov edi, dword ptr [ edi]
    call dword ptr [ edi + tCollection_Error]
  end;


constructor tCollection.Init( aLimit, aDelta: tIndex);
  begin
    inherited Init();
    Items := nil;
    Count := 0;
    Limit := 0;
    Delta := aDelta;
    SetLimit( aLimit);
  end;

destructor tCollection.Done;
  begin
    FreeAll();
    SetLimit( 0);
    inherited Done();
  end;

constructor tCollection.Load( var S: tStream);
  var
    C, I: tIndex;
  begin
    S.Read( Count, SizeOf( tIndex) * 3);
    Items := nil;
    C := Count;
    I := Limit;
    Count := 0;
    Limit := 0;
    SetLimit( I);
    Count := C;
    for I := 0 to C - 1 do AtPut( I, GetItem( S));
  end;

procedure tCollection.Store( var S: tStream);

  procedure DoPutItem( P: Pointer);
    begin
      PutItem( S, P);
    end;

  begin
    S.Write( Count, SizeOf( tIndex) * 3);
    ForEach( @DoPutItem);
  end;

function tCollection.At( Index: tIndex): Pointer; assembler;
  asm
    mov edi, dword ptr [ Self]
    mov ebx, Index
    cmp ebx, [ edi].tCollection.Count
    jae @@Error
    mov esi, [ edi].tCollection.Items
    mov eax, dword ptr [ esi + ebx * 4]
    jmp @@Exit

  @@Error:
    mov eax, coIndexError
    call CollectionError
    xor eax, eax

  @@Exit:
  end;

procedure tCollection.AtDelete( Index: tIndex); assembler;
  asm
    mov edi, dword ptr [ Self]
    mov ebx, Index
    mov ecx, [ edi].tCollection.Count
    sub ecx, ebx
    jbe @@Error

    dec [ edi].tCollection.Count
    dec ecx
    je  @@Exit
    mov esi, [ edi].tCollection.Items
    lea edi, [ esi + ebx * 4]
    lea esi, [ edi + 4]
    cld
    rep movsd
    jmp @@Exit

  @@Error:
    mov eax, coIndexError
    call CollectionError
    xor eax, eax

  @@Exit:
  end;

procedure tCollection.AtFree( Index: tIndex);
  var
    Item: Pointer;
  begin
    Item := At( Index);
    AtDelete( Index);
    FreeItem( Item);
  end;

procedure tCollection.AtInsert( Index: tIndex; Item: Pointer); assembler;
  asm
    mov edi, dword ptr [ Self]
    mov ebx, Index
    or  ebx, ebx
    js  @@IndexError
    mov eax, [ edi].tCollection.Count
    sub eax, ebx
    jl  @@IndexError
    push eax
    mov ecx, [ edi].tCollection.Limit
    cmp ecx, [ edi].tCollection.Count
    jg  @@Insert
    push ecx
    push ebx
    push edi
    add ecx, [ edi].tCollection.Delta
    push edi
    push ecx
    mov edi, dword ptr [ edi]
    call dword ptr [ edi + tCollection_SetLimit]
    pop edi
    pop ebx
    pop ecx
    cmp ecx, [ edi].tCollection.Limit
    je  @@Overflow
  @@Insert:
    pop ecx
    mov esi, [ edi].tCollection.Items
    mov eax, [ edi].tCollection.Count
    inc [ edi].tCollection.Count
    lea edi, [ esi + eax * 4]
    lea esi, [ edi - 4]
    std
    rep movsd
    mov eax, Item
    stosd
    cld
    jmp @@Exit

  @@IndexError:
    mov eax, coIndexError
    jmp @@Error
  @@Overflow:
    mov eax, coOverflow
  @@Error:
    call CollectionError

  @@Exit:
  end;

procedure tCollection.AtPut( Index: tIndex; Item: Pointer); assembler;
  asm
    mov edi, dword ptr [ Self]
    mov ebx, Index
    cmp ebx, [ edi].tCollection.Count
    jae @@Error
    mov esi, [ edi].tCollection.Items
    mov eax, Item
    mov dword ptr [ esi + ebx * 4], eax
    jmp @@Exit

  @@Error:
    mov eax, coIndexError
    call CollectionError

  @@Exit:
  end;

procedure tCollection.Delete( Item: Pointer);
  begin
    AtDelete( IndexOf( Item));
  end;

procedure tCollection.DeleteAll;
  begin
    Count := 0;
  end;

procedure tCollection.Error( Code, Info: Integer);
  begin
    RunError( 212 - Code);
  end;

function tCollection.FirstThat( Test: Pointer): Pointer; assembler;
  asm
    cmp &Test, 0
    je  @@Exit
    mov edi, dword ptr [ Self]
    mov ecx, [ edi].tCollection.Count
    jcxz @@NotFound
    mov esi, [ edi].tCollection.Items

  @@Loop:
    cld
    lodsd
    push eax
    push esi
    push ecx

    push eax
    push dword ptr [ ebp]
    call &Test

    pop ecx
    pop esi
    pop edx
    or  eax, eax
    jne @@Exit
    loop @@Loop

  @@NotFound:
    xor edx, edx

  @@Exit:
    mov eax, edx
  end;

procedure tCollection.ForEach( Action: Pointer); assembler;
  asm
    mov ebx, Action
    or  ebx, ebx
    je  @@Exit
    mov edi, dword ptr [ Self]
    mov ecx, [ edi].tCollection.Count
    jcxz @@Exit
    mov esi, [ edi].tCollection.Items
  @@Loop:
    cld
    lodsd
    push esi
    push ecx

    push eax
    push dword ptr [ ebp]
    call Action

    pop ecx
    pop esi
    loop @@Loop

  @@Exit:
  end;

procedure tCollection.Free( Item: Pointer);
  begin
    Delete( Item);
    FreeItem( Item);
  end;

procedure tCollection.FreeAll;
  var
    I: tIndex;
  begin
    for I := 0 to Count - 1 do
      FreeItem( At( I));
    Count := 0;
  end;

procedure tCollection.FreeItem( Item: Pointer);
  begin
    if Assigned( Item) then
      Dispose( pObject( Item), Done() );
  end;

function tCollection.GetItem( var S: tStream): Pointer;
  begin
    GetItem := S.Get();
  end;

function tCollection.IndexOf( Item: Pointer): tIndex; assembler;
  asm
    mov edi, dword ptr [ Self]
    mov ecx, [ edi].tCollection.Count
    jcxz @@NotFound
    mov edi, [ edi].tCollection.Items
    cld
    mov eax, Item
    mov ebx, ecx
    repne scasd
    jne @@NotFound
    mov eax, ebx
    sub eax, ecx
    dec eax
    jmp @@Exit

  @@NotFound:
    mov eax, -1

  @@Exit:
  end;

procedure tCollection.Insert( Item: Pointer);
  begin
    AtInsert( Count, Item);
  end;

function tCollection.LastThat( Test: Pointer): Pointer; assembler;
  asm
    cmp &Test, 0
    je  @@Exit
    mov edi, dword ptr [ Self]
    mov ecx, [ edi].tCollection.Count
    jcxz @@NotFound
    mov esi, [ edi].tCollection.Items
    lea esi, [ esi + ecx * 4 - 4 ]

  @@Loop:
    std
    lodsd
    push eax
    push esi
    push ecx

    push eax
    push dword ptr [ ebp]
    call &Test

    pop ecx
    pop esi
    pop edx
    or  eax, eax
    jne @@Exit
    loop @@Loop

  @@NotFound:
    xor edx, edx

  @@Exit:
    mov eax, edx
  end;

procedure tCollection.Pack; assembler;
  asm
    mov edi, dword ptr [ Self]
    mov ecx, [ edi].tCollection.Count
    jcxz @@Exit
    mov esi, [ edi].tCollection.Items
    mov edi, esi
    mov edx, edi

  @@Loop:
    lodsd
    or  eax, eax
    je  @@1
    stosd
  @@1:
    loop @@Loop

    mov eax, edi
    sub eax, edx
    shr eax, 2
    mov edi, dword ptr [ Self]
    mov [ edi].tCollection.Count, eax

  @@Exit:
  end;

procedure tCollection.PutItem( var S: tStream; Item: Pointer);
  begin
    S.Put( Item);
  end;

procedure tCollection.SetLimit( aLimit: tIndex);
  var
    NewItems: pItemList;
  begin
    if aLimit < Count then
      aLimit := Count;
    if aLimit > MaxCollectionSize then
      aLimit := MaxCollectionSize;
    if aLimit <> Limit then
      begin
        if aLimit > 0 then
          begin
            GetMem( NewItems, aLimit * SizeOf( Pointer));
            if (Count > 0) and Assigned( Items) then
              Move( Items^, NewItems^, Count * SizeOf( Pointer));
          end
        else
          NewItems := nil;
        if Limit > 0 then
          FreeMem( Items, Limit * SizeOf( Pointer));
        Items := NewItems;
        Limit := aLimit;
      end;
  end;


{ tSortedCollection }
constructor tSortedCollection.Init( aLimit, aDelta: tIndex);
  begin
    inherited Init( aLimit, aDelta);
    Duplicates := False;
  end;
  
constructor tSortedCollection.Load( var S: tStream);
  begin
    inherited Load( S);
    S.Read( Duplicates, SizeOf( Duplicates));
  end;

procedure tSortedCollection.Store( var S: tStream);
  begin
    inherited Store( S);
    S.Write( Duplicates, SizeOf( Duplicates));
  end;

function tSortedCollection.Compare( Key1, Key2: Pointer): LongInt;
  begin
    Abstract();
  end;

function tSortedCollection.IndexOf( Item: Pointer): tIndex;
  var
    I: tIndex;
  begin
    IndexOf := -1;
    if Search( KeyOf( Item), I) then
      begin
        if Duplicates then
          while (I < Count) and (Item <> Items^[ I]) do
            Inc( I);
        if I < Count then
          IndexOf := Count;
      end;
  end;

procedure tSortedCollection.Insert( Item: Pointer);
  var
    I: tIndex;
  begin
    if not Search( KeyOf( Item), I) or Duplicates then
      AtInsert( I, Item);
  end;

function tSortedCollection.KeyOf( Item: Pointer): Pointer;
  begin
    KeyOf := Item;
  end;

function tSortedCollection.Search( Key: Pointer; var Index: tIndex): Boolean;
  var
    L, H, I: tIndex;
    C: LongInt;
  begin
    L := 0;
    H := Count - 1;
    Search := False;
    while L <= H do
      begin
        I := (L + H) div 2;
        C := Compare( KeyOf( Items^[ I]), Key);
        if C < 0 then
          L := I + 1
        else
          begin
            H := I - 1;
            if C = 0 then
              begin
                Search := True;
                if not Duplicates then
                  L := I;
              end;
          end;
      end;
    Index := L;
  end;


{ tStringCollection }
function tStringCollection.Compare( Key1, Key2: Pointer): LongInt; assembler;
  asm
    mov esi, dword ptr [ Key1]
    mov edi, dword ptr [ Key2]
    movzx edx, byte ptr [edi]
    inc edi
    movzx ebx, byte ptr [esi]
    inc esi
    mov ecx, ebx
    cmp ecx, edx
    jbe @@1
    mov ecx, edx
  @@1:
    jcxz @@eq
    repe cmpsb
    movzx eax, byte ptr [esi - 1]
    movzx ecx, byte ptr [edi - 1]
    sub eax, ecx
    jnz @@Exit
    {ja @@lower
    jb @@greater}
  @@eq:
    mov eax, ebx
    sub eax, edx
    jmp @@Exit
    {cmp edx, ebx
    ja @@lower
    jb @@greater
    xor eax, eax
    jmp @@exit}
  @@lower:
    mov eax, -1
    jmp @@exit
  @@greater:
    mov eax, 1
  @@exit:
  end;

function tStringCollection.GetItem( var S: tStream): Pointer;
  begin
    GetItem := S.ReadStr();
  end;

procedure tStringCollection.PutItem( var S: tStream; Item: Pointer);
  begin
    S.WriteStr( Item);
  end;

procedure tStringCollection.FreeItem( Item: Pointer);
  begin
    DisposeStr( Item);
  end;


{ tStrCollection }

function tStrCollection.Compare( Key1, Key2: Pointer): LongInt;
  begin
    Result := StrComp( Key1, Key2);
  end;

function tStrCollection.GetItem( var S: tStream): Pointer;
  begin
    Result := S.StrRead;
  end;

procedure tStrCollection.PutItem( var S: tStream; Item: Pointer);
  begin
    S.StrWrite( Item);
  end;

procedure tStrCollection.FreeItem( Item: Pointer);
  begin
    StrDispose( Item);
  end;


{ Abstract }
procedure Abstract;
  begin
    RunError( 211);
  end;


procedure RegisterType( var S: tStreamRec); assembler;
  asm
    mov edi, dword ptr [ S]
    or  edi, edi
    je  @@RegisterError
    mov eax, [edi].tStreamRec.ObjType
    or  eax, eax
    je  @@RegisterError
    mov esi, StreamTypes

  @@1:
    or  esi, esi
    je  @@Register
    cmp eax, [esi].tStreamRec.ObjType
    je  @@RegisterError
    mov esi, [esi].tStreamRec.Next
    jmp @@1

  @@RegisterError:
    push 212
    call RunError

  @@Register:
    mov eax, StreamTypes
    mov [edi].tStreamRec.Next, eax
    mov StreamTypes, edi
  end;


  { pString routines }
function NewStr( const Val: String): pString;
  begin
    if Val <> '' then
      begin
        GetMem( NewStr, Length( Val) + 1);
        NewStr^ := Val;
      end
    else
      NewStr := nil;
  end;

procedure DisposeStr( P: pString);
  begin
    if Assigned( P) then
      FreeMem( P, Length( P^) + 1);
  end;


procedure RegisterObjects;
  begin
    RegisterType( RCollection);
    RegisterType( RStringCollection);
    RegisterType( RStrCollection);
  end;

end.