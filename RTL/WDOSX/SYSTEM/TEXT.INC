
procedure TextInOut( var TextFile: TextRec);
  begin
    case TextFile.Mode of
      fmOutput:
        begin
          WriteBufToFile( TextFile.Handle, TextFile.BufPtr, TextFile.BufPos);
          TextFile.BufPos := 0;
        end;
      fmInput:
        begin
          TextFile.BufEnd := ReadFromFile( TextFile.Handle, TextFile.BufPtr, TextFile.BufSize);
          TextFile.BufPos := 0;
        end;
    end;
  end;

procedure TextClose( var TextFile: TextRec);
  begin
    asm
      mov edi, dword ptr [ TextFile]
      push edi
      call dword ptr [edi].TextRec.FlushFunc;
    end;
    CloseFile( TextFile.Handle);
  end;

procedure TextOpen( var TextFile: TextRec);
  var
    Name: array [0..255] of Char;
  begin
    TextFile.InOutFunc := @TextInOut;
    TextFile.FlushFunc := @TextInOut;
    TextFile.CloseFunc := @TextClose;
    TextFile.BufSize := SizeOf( TextBuf);
    TextFile.BufPtr := @TextFile.Buffer;
    TextFile.BufPos := 0;
    TextFile.BufEnd := 0;
    {ToASCIIZ( TextFile.Name, @Name);}
    case TextFile.Mode of
      fmInput:
        TextFile.Handle := OpenFile( @TextFile.Name, $3D00);
      fmOutPut:
        TextFile.Handle := OpenFile( @TextFile.Name, $3C00);
      fmInOut:
        TextFile.Handle := OpenFile( @Name, $3D01);
    end;
  end;


function CurChar( var TextFile: TextRec): Char;
  begin
    if TextFile.Mode = fmInput then
      begin
        if TextFile.BufEnd <= TextFile.BufPos then
          asm
                mov edi, dword ptr [TextFile]
                push edi
                call [edi].TextRec.InOutFunc
          end;
        if TextFile.BufEnd > TextFile.BufPos then
          CurChar := TextFile.BufPtr^[TextFile.BufPos]
        else
          CurChar := #26;
      end;
  end;

function NextChar( var TextFile: TextRec): Char;
  begin
    if TextFile.Mode = fmInput then
      begin
        Inc( TextFile.BufPos);
        NextChar := CurChar( TextFile);
      end;
  end;


procedure WriteString( var TextFile: Text; const S: String; Len: LongInt); 'writestring';
  var
    CurPos, Count: LongInt;
  begin
    if TextRec( TextFile).Mode = fmOutPut then
      begin
        if TextRec( TextFile).BufPos > 0 then
          asm
            mov edi, dword ptr [TextFile]
            push edi
            call [edi].TextRec.FlushFunc
          end;
        if Byte( S[0]) < Len then
          begin
            Count := Len - Byte( S[0]);
            while Count > 0 do
              begin
                CurPos := TextRec( TextFile).BufSize - TextRec( TextFile).BufPos;
                if CurPos > Count then
                  CurPos := Count;
                FillChar( TextRec( TextFile).BufPtr^[ TextRec( TextFile).BufPos], CurPos, ' ');
                Dec( Count, CurPos);
                Inc( TextRec( TextFile).BufPos, CurPos);
                asm
                  mov edi, dword ptr [TextFile]
                  push edi
                  call [edi].TextRec.InOutFunc
                end;
              end;
          end;
        CurPos := 1;
        while Byte( S[0]) >= CurPos do
          begin
            Count := TextRec( TextFile).BufSize - TextRec( TextFile).BufPos;
            if Byte( S[0]) - CurPos + 1 < Count then
              Count := Byte( S[0]) - CurPos + 1;
            Move( S[ CurPos], TextRec( TextFile).BufPtr^[ TextRec( TextFile).BufPos], Count);
            Inc( TextRec( TextFile).BufPos, Count);
            Inc( CurPos, Count);
            asm
              mov edi, dword ptr [TextFile]
              push edi
              call [edi].TextRec.InOutFunc
            end;
          end;
      end;
  end;


procedure WriteChar( var TextFile: Text; C: Char; Len: LongInt); 'writechar';
  begin
    WriteString( TextFile, C, Len);
  end;

procedure WriteSInt( var TextFile: Text; L: LongInt; Len: LongInt); 'writesint';
  var
    S: String;
  begin
    SIntToStr( L, S);
    WriteString( TextFile, S, Len);
  end;

procedure WriteUInt( var TextFile: Text; D: DWord; Len: LongInt); 'writeuint';
  var
    S: String;
  begin
    UIntToStr( D, S);
    WriteString( TextFile, S, Len);
  end;


procedure WriteReal( var TextFile: Text; R: Extended; Len, Digs: LongInt); 'writereal';
  var
    S: String;
  begin
    RealToStr( R, S, Digs);
    WriteString( TextFile, S, Len);
  end;


procedure WriteBoolean( var TextFile: Text; B: Boolean; Len: LongInt); 'writeboolean';
  begin
    if B then
      WriteString( TextFile, TrueString, Len)
    else
      WriteString( TextFile, FalseString, Len);
  end;


procedure WriteLine( var TextFile: Text); 'writeline';
  const
    EOL: String[2] = #13#10;
  begin
    WriteString( TextFile, EOL, 2);
  end;


procedure ReadString( var TextFile: TextRec; var S: String; MaxLen: LongInt); 'readstring';
  var
    I: LongInt;
  begin
    I := 0;
    S[0] := #0;
    if TextFile.Mode = fmInput then
      begin
        while I < MaxLen do
          begin
            if TextFile.BufPos >= TextFile.BufEnd then
              asm
                mov edi, dword ptr [TextFile]
                push edi
                call [edi].TextRec.InOutFunc
              end;
            if TextFile.BufPos < TextFile.BufEnd then
              case TextFile.BufPtr^[TextFile.BufPos] of
                #13,
                #26:
                  begin
                    break;
                  end;
                else
                  begin
                    Inc( I);
                    S[ I] := TextFile.BufPtr^[ TextFile.BufPos];
                    Inc( TextFile.BufPos);
                  end;
              end
            else
              begin
                break;
              end;
          end;
      end;
    S[0] := Char( I);
  end;

function ReadChar( var TextFile: TextRec): Char; 'readchar';
  begin
    ReadChar := #0;
    if TextFile.Mode = fmInput then
      begin
        if TextFile.BufPos >= TextFile.BufEnd then
          asm
            mov edi, dword ptr [TextFile]
            push edi
            call [edi].TextRec.InOutFunc
          end;
        if TextFile.BufPos < TextFile.BufEnd then
          begin
            ReadChar := TextFile.BufPtr^[ TextFile.BufPos];
            Inc( TextFile.BufPos);
           end
        else
          ReadChar := #26;
      end;
  end;

function ReadInt( var TextFile: TextRec): LongInt; 'readint';
  var
    S: String;
    L: LongInt;
    Code: Integer;
  begin
    if CurChar( TextFile) in [#0..#32, #255] then
      while NextChar( TextFile) in [#0..#32, #255] do
        if CurChar( TextFile) = #26 then break;
    S := '';
    while not ( CurChar( TextFile) in [#0..#32, #255]) do
      begin
        S := S + CurChar( TextFile);
        NextChar( TextFile);
      end;
    Val( S, L, Code);
    if Code = 0 then
      ReadInt := L
    else
      begin
        RunError( 106);
        ReadInt := 0;
      end;
  end;

function ReadReal( var TextFile: TextRec): Extended; 'readreal';
  var
    S: String;
    E: Extended;
    Code: Integer;
  begin
    if CurChar( TextFile) in [#0..#32, #255] then
      while NextChar( TextFile) in [#0..#32, #255] do
        if CurChar( TextFile) = #26 then break;
    S := '';
    while not ( CurChar( TextFile) in [#0..#32, #255]) do
      begin
        S := S + CurChar( TextFile);
        NextChar( TextFile);
      end;
    Val( S, E, Code);
    if Code = 0 then
      ReadReal := E
    else
      begin
        RunError( 106);
        ReadReal := 0;
      end;
  end;

procedure ReadLine( var TextFile: TextRec); 'readline';
  var
    C: Char;
  begin
    if TextFile.Mode = fmInput then
      begin
        C := CurChar( TextFile);
        while (C <> #26) and (C <> #13) and (C <> #10) do
          begin
            C := NextChar( TextFile);
            {if TextFile.BufPos >= TextFile.BufEnd then
              asm
                mov edi, dword ptr [TextFile]
                push edi
                call [edi].TextRec.InOutFunc
              end;
            if TextFile.BufPos < TextFile.BufEnd then
              if TextFile.BufPtr^[TextFile.BufPos] = #13 then
                begin
                  Inc( TextFile.BufPos);
                  if (TextFile.BufPos < TextFile.BufEnd)
                    and (TextFile.BufPtr^[TextFile.BufPos] = #10) then
                    Inc( TextFile.BufPos);
                  break;
                end
              else
                begin
                  Inc( TextFile.BufPos);
                end
            else
              break;}
          end;
        if C = #13 then
          if NextChar( TextFile) = #10 then Inc( TextFile.BufPos);
      end;
  end;

procedure AssignText( var TextFile: Text; const FileName: String); 'assigntext';
  begin
    ToASCIIZ( FileName, @TextRec( TextFile).Name);
    {TextRec( TextFile).Name := FileName;}
    TextRec( TextFile).Mode := fmClosed;
    TextRec( TextFile).OpenFunc := @TextOpen;
  end;

procedure Reset( var TextFile: Text);
  begin
    TextRec( TextFile).Mode := fmInput;
    asm
      mov edi, dword ptr [ TextFile]
      push edi
      call dword ptr [edi].TextRec.OpenFunc
    end;
  end;

procedure ReWrite( var TextFile: Text);
  begin
    TextRec( TextFile).Mode := fmOutput;
    asm
      mov edi, dword ptr [ TextFile]
      push edi
      call dword ptr [edi].TextRec.OpenFunc
    end;
  end;

procedure Close( var TextFile: Text);
  begin
    if TextRec( TextFile).Mode <> fmClosed then
      asm
        mov edi, dword ptr [ TextFile]
        push edi
        call dword ptr [edi].TextRec.FlushFunc

        mov edi, dword ptr [ TextFile]
        push edi
        call dword ptr [edi].TextRec.CloseFunc
      end;
    TextRec( TextFile).Mode := fmClosed;
  end;

procedure Append( var TextFile: Text);
  begin
    TextRec( TextFile).Mode := fmInOut;
    asm
      mov edi, dword ptr [ TextFile]
      push edi
      call dword ptr [edi].TextRec.OpenFunc
    end;
    TextRec( TextFile).Mode := fmOutput;
  end;

procedure Flush( var TextFile: Text);
  begin
    if TextRec( TextFile).Mode = fmOutput then
      asm
        mov edi, dword ptr [ TextFile]
        push edi
        call dword ptr [edi].TextRec.InOutFunc
      end;
  end;

function EOF( var TextFile: Text): Boolean;
  begin
    EOF := CurChar( TextRec(TextFile)) = #26;
  end;

function EOLn( var TextFile: Text): Boolean;
  begin
    EOLn := CurChar( TextRec(TextFile)) = #13;
  end;

function SeekEOF( var TextFile: Text): Boolean;
  begin
    while CurChar( TextRec( TextFile)) = ' ' do
      NextChar( TextRec( TextFile));
    SeekEOF := CurChar( TextRec(TextFile)) = #26;
  end;

function SeekEOLn( var TextFile: Text): Boolean;
  begin
    while CurChar( TextRec( TextFile)) = ' ' do
      NextChar( TextRec( TextFile));
    SeekEOLn := CurChar( TextRec(TextFile)) = #13;
  end;

procedure ReName( var TextFile: Text; const NewName: String);
  var
    Buf1, Buf2: array [0..255] of Char;
  begin
    if TextRec( TextFile).Mode = fmClosed then
      begin
        {ToASCIIZ( TextRec( TextFile).Name, @Buf1);}
        ToASCIIZ( NewName, @Buf2);
        ReNameFile( @TextRec( TextFile).Name, @Buf2);
      end;
  end;

procedure Erase( var TextFile: Text);
  var
    Buf: array [0..255] of Char;
  begin
    if TextRec( TextFile).Mode = fmClosed then
      begin
        {ToASCIIZ( TextRec( TextFile).Name, @Buf);}
        DeleteFile( @TextRec( TextFile).Name);
      end;
  end;

procedure SetTextBuf( var TextFile: Text; var Buffer; Size: LongInt); assembler;
  asm
    mov edi, dword ptr [TextFile]
    or  edi, edi
    jz  @@exit
    mov eax, dword ptr [Buffer]
    or  eax, eax
    jz  @@exit
    mov edx, dword ptr [Size]
    or  edx, edx
    jz  @@exit
    mov dword ptr [edi].TextRec.BufPtr, eax
    mov dword ptr [edi].TextRec.BufSize, edx
  @@exit:
  end;

