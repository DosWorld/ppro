{                    GNU LESSER GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Full text of license:
 https://www.gnu.org/licenses/lgpl-3.0.en.html

 (c) Copyright 2022 DosWord
 (c) Copyright 1997-1998 Iggor Khachko - hachko@icl.kazan.su }

function GetFileData( Handle: Word; var Pos, Size: LongInt): LongInt; Assembler;
  asm
    movzx ebx, Handle
    mov eax, $4201
    xor edx, edx
    mov ecx, edx
    int $21
    jc @@error
    mov edi, dword ptr [ Pos]
    mov word ptr [ edi], ax
    mov word ptr [ edi + 2], dx
    push ax
    push dx

    movzx ebx, Handle
    mov eax, $4202
    xor edx, edx
    mov ecx, edx
    int $21
    jc @@error
    mov edi, dword ptr [ Size]
    mov word ptr [ edi], ax
    mov word ptr [ edi + 2], dx

    pop cx
    pop dx
    movzx ebx, Handle
    mov eax, $4200
    int $21
    jc @@error
    xor eax, eax
    jmp @@exit

  @@error:
    mov InOutRes, ax
    movzx eax, ax

  @@exit:
  end;

function FileSeek( Handle: Word; Pos: LongInt): LongInt; Assembler;
  asm
    mov eax, $4200
    movzx ebx, Handle
    mov edx, Pos
    int $21
    jc @@error
    xor eax, eax
    jmp @@exit
  @@error:
    mov InOutRes, ax
    movzx eax, ax
  @@exit:
  end;

procedure AssignTyped( var F: FileRec; const FileName: String; RecSize: LongInt); 'assigntyped';
  begin
    F.Mode := fmClosed;
    F.RecSize := RecSize;
    ToASCIIZ( FileName, @F.Name);
  end;

procedure ReSet( var F: TypedFile);
  begin
    FileRec( F).Mode := fmInOut;
    FileRec( F).Handle := OpenFile( @FileRec( F).Name, $3D00 + FileMode);
  end;

procedure ReWrite( var F: TypedFile);
  begin
    FileRec( F).Mode := fmInOut;
    FileRec( F).Handle := OpenFile( @FileRec( F).Name, $3C00);
  end;

procedure Close( var F: TypedFile);
  begin
    CloseFile( FileRec( F).Handle);
  end;

procedure WriteRecord( var F: FileRec; var _Record); 'writerecord';
  begin
    WriteBufToFile( F.Handle, @_Record, F.RecSize);
  end;

procedure ReadRecord( var F: FileRec; var _Record); 'readrecord';
  begin
    ReadFromFile( F.Handle, @_Record, F.RecSize);
  end;

function EOF( var F: TypedFile): Boolean;
  var
    Size, Pos: LongInt;
  begin
    EOF := (GetFileData( FileRec( F).Handle, Pos, Size) <> 0)  or
      (IOResult() <> 0) or ( Size <= Pos );
  end;

procedure Erase( var F: TypedFile);
  begin
    if FileRec( F).Mode = fmClosed then
      begin
        DeleteFile( @FileRec( F).Name);
      end;
  end;

procedure ReName( var F: TypedFile; const NewName: String);
  var
    Buf: array [0..255] of Char;
  begin
    if FileRec( F).Mode = fmClosed then
      begin
        ToASCIIZ( NewName, @Buf);
        ReNameFile( @FileRec( F).Name, @Buf);
      end;
  end;

procedure Seek( var F: TypedFile; NewPos: LongInt);
  begin
    if FileRec( F).Mode = fmInOut then
      FileSeek( FileRec( F).Handle, NewPos * FileRec( F).RecSize);
  end;

function FilePos( var F: TypedFile): LongInt;
  var
    Pos, Size: LongInt;
  begin
    FilePos := -1;
    if FileRec( F).Mode = fmInOut then
      if GetFileData( FileRec( F).Handle, Pos, Size) = 0 then
        FilePos := Pos div FileRec( F).RecSize;
  end;

function FileSize( var F: TypedFile): LongInt;
  var
    Pos, Size: LongInt;
  begin
    FileSize := -1;
    if FileRec( F).Mode = fmInOut then
      if GetFileData( FileRec( F).Handle, Pos, Size) = 0 then
        FileSize := Size div FileRec( F).RecSize;
  end;

procedure Truncate( var F: TypedFile);
  begin
    if FileRec( F).Mode = fmInOut then
      asm
        mov edi, dword ptr [F]
        mov bx, word ptr [F].FileRec.Handle
        xor ecx, ecx
        mov ax, $4000
        int $21
      end;
  end;

procedure AssignUntyped( var F: FileRec; const FileName: String); 'assignuntyped';
  begin
    F.Mode := fmClosed;
    F.RecSize := 1;
    ToASCIIZ( FileName, @F.Name);
  end;

procedure Reset( var F: File);
  begin
    FileRec( F).Mode := fmInOut;
    FileRec( F).RecSize := 1;
    FileRec( F).Handle := OpenFile( @FileRec( F).Name, $3D02);
  end;

procedure Reset( var F: File; RecSize: LongInt);
  begin
    FileRec( F).Mode := fmInOut;
    FileRec( F).RecSize := RecSize;
    FileRec( F).Handle := OpenFile( @FileRec( F).Name, $3D02);
  end;

procedure ReWrite( var F: File);
  begin
    FileRec( F).Mode := fmInOut;
    FileRec( F).RecSize := 1;
    FileRec( F).Handle := OpenFile( @FileRec( F).Name, $3C00);
  end;

procedure ReWrite( var F: File; RecSize: LongInt);
  begin
    FileRec( F).Mode := fmInOut;
    FileRec( F).RecSize := RecSize;
    FileRec( F).Handle := OpenFile( @FileRec( F).Name, $3C00);
  end;

procedure Close( var F: File);
  begin
    CloseFile( FileRec( F).Handle);
  end;

procedure BlockRead( var F: File; var Buf; Count: LongInt;
    var Result: LongInt);
  begin
    Result := ReadFromFile( FileRec( F).Handle, @Buf,
      Count * FileRec( F).RecSize) div FileRec( F).RecSize;
  end;

procedure BlockRead( var F: File; var Buf; Count: LongInt);
  var
    Res: LongInt;
  begin
    BlockRead( F, Buf, Count, Res);
  end;

procedure BlockWrite( var F: File; var Buf; Count: LongInt;
    var Result: LongInt);
  begin
    Result := WriteBufToFile( FileRec( F).Handle, @Buf,
      Count * FileRec( F).RecSize) div FileRec( F).RecSize;
  end;

procedure BlockWrite( var F: File; var Buf; Count: LongInt);
  var
    Res: LongInt;
  begin
    BlockWrite( F, Buf, Count, Res);
  end;

function EOF( var F: File): Boolean;
  var
    Size, Pos: LongInt;
  begin
    EOF := (GetFileData( FileRec( F).Handle, Pos, Size) <> 0) 
      or ( Size <= Pos );
  end;

procedure Erase( var F: File);
  begin
    if FileRec( F).Mode = fmClosed then
      begin
        DeleteFile( @FileRec( F).Name);
      end;
  end;

procedure ReName( var F: File; const NewName: String);
  var
    Buf: array [0..255] of Char;
  begin
    if FileRec( F).Mode = fmClosed then
      begin
        ToASCIIZ( NewName, @Buf);
        ReNameFile( @FileRec( F).Name, @Buf);
      end;
  end;

procedure Seek( var F: file; NewPos: LongInt);
  begin
    if FileRec( F).Mode = fmInOut then
      FileSeek( FileRec( F).Handle, NewPos * FileRec( F).RecSize);
  end;

function FilePos( var F: file): LongInt;
  var
    Pos, Size: LongInt;
  begin
    FilePos := -1;
    if FileRec( F).Mode = fmInOut then
      if GetFileData( FileRec( F).Handle, Pos, Size) = 0 then
        FilePos := Pos div FileRec( F).RecSize;
  end;

function FileSize( var F: file): LongInt;
  var
    Pos, Size: LongInt;
  begin
    FileSize := -1;
    if FileRec( F).Mode = fmInOut then
      if GetFileData( FileRec( F).Handle, Pos, Size) = 0 then
        FileSize := Size div FileRec( F).RecSize;
  end;

procedure Truncate( var F: file);
  begin
    if FileRec( F).Mode = fmInOut then
      asm
        mov edi, dword ptr [F]
        mov bx, word ptr [F].FileRec.Handle
        xor ecx, ecx
        mov ax, $4000
        int $21
      end;
  end;
