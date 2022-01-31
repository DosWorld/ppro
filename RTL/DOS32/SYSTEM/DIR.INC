{                    GNU LESSER GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Full text of license:
 https://www.gnu.org/licenses/lgpl-3.0.en.html

 (c) Copyright 2022 DosWord
 (c) Copyright 1997-1998 Iggor Khachko - hachko@icl.kazan.su }

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
  end;

