
procedure ChDir( const Dir: String);
  var
    Buf: array [0..255] of char;
  begin
    ToASCIIZ( Dir, @Buf);
    asm
      mov ah, $3b
      lea edx, Buf
      int $21
      jc @@exit
      xor ax, ax
    @@exit:
      mov InOutRes, ax
    end;
  end;

procedure MkDir( const Dir: String);
  var
    Buf: array [0..255] of char;
  begin
    ToASCIIZ( Dir, @Buf);
    asm
      mov ah, $39
      lea edx, Buf
      int $21
      jc @@exit
      xor ax, ax
    @@exit:
      mov InOutRes, ax
    end;
  end;

procedure RmDir( const Dir: String);
  var
    Buf: array [0..255] of char;
  begin
    ToASCIIZ( Dir, @Buf);
    asm
      mov ah, $3A
      lea edx, Buf
      int $21
      jc @@exit
      xor ax, ax
    @@exit:
      mov InOutRes, ax
    end;
  end;

procedure GetDir( Drive: Byte; var Dir: String);
  var
    Buf: array [0..255] of Char;
  begin
    asm
      mov al, Drive
      or  al, al
      jnz @@1
      mov eax, $1900
      int $21
      inc al
      mov Drive, al

    @@1:
      mov ah, $47
      mov dl, Drive
      lea esi, Buf
      int $21
      jc @@exit
      xor ax, ax
    @@exit:
      mov InOutRes, ax
    end;
    if InOutRes = 0 then
      FromASCIIZ( @Buf, Dir);
    Dir := Chr( Drive + Ord( 'A') - 1) + ':\' + Dir;
  end;

        