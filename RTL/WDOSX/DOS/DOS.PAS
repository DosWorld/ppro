{                    GNU LESSER GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Full text of license:
 https://www.gnu.org/licenses/lgpl-3.0.en.html

 (c) Copyright 2022 DosWord
 (c) Copyright 1997-1998 Iggor Khachko - hachko@icl.kazan.su }

unit Dos;

interface

{$IFNDEF WDOSX}
{$ERROR Must be WDOSX target}
{$ENDIF}

{$IFNDEF PPRO}
{$ERROR Requires Pascal Pro compiler}
{$ENDIF}

const

{ Flags bit masks }

  FCarry     = $0001;
  FParity    = $0004;
  FAuxiliary = $0010;
  FZero      = $0040;
  FSign      = $0080;
  FOverflow  = $0800;

{ File mode magic numbers }

  fmClosed = $D7B0;
  fmInput  = $D7B1;
  fmOutput = $D7B2;
  fmInOut  = $D7B3;

{ File attribute constants }

  ReadOnly  = $01;
  Hidden    = $02;
  SysFile   = $04;
  VolumeID  = $08;
  Directory = $10;
  Archive   = $20;
  AnyFile   = $3F;

type

{ String types }

  ComStr  = string[127];        { Command line string }
  PathStr = string[79];         { File pathname string }
  DirStr  = string[67];         { Drive and directory string }
  NameStr = string[8];          { File name string }
  ExtStr  = string[4];          { File extension string }


{ Typed-file and untyped-file record }

  FileRec = record
              Handle: Word;
              Mode: Word;
              RecSize: Word;
              _Private: array[1..26] of Byte;
              UserData: array[1..16] of Byte;
              Name: array[0..79] of Char;
            end;

{ Textfile record }

  TextBuf = array[0..127] of Char;
  TextRec = record
              Handle: Word;
              Mode: Word;
              BufSize: Word;
              _Private: Word;
              BufPos: Word;
              BufEnd: Word;
              BufPtr: ^TextBuf;
              OpenFunc: Pointer;
              InOutFunc: Pointer;
              FlushFunc: Pointer;
              CloseFunc: Pointer;
              UserData: array[1..16] of Byte;
              Name: array[0..79] of Char;
              Buffer: TextBuf;
            end;

{ Search record used by FindFirst and FindNext }

  SearchRec = record
                Fill: array[1..21] of Byte;
                Attr: Byte;
                Time: Longint;
                Size: Longint;
                Name: string[12];
              end;


{ Registers record used by Intr and MsDos }

  registers = record
    case integer of
      0: (EDI, ESI, EBP, Reserved1, EBX, EDX, ECX, EAX: LongInt);
      1: (DI, Reserved2, SI, Reserved3, BP, Reserved4, Reserved5, Reserved6,
          BX, Reserved7, DX, Reserved8, CX, Reserved9, AX, Reserved10,
          Flags, ES, DS, FS, GS, IP, CS, SP, SS: Word);
      2: (Reserved11: array [0..15] of Byte;
          BL, BH, Reserved12, Reserved13, DL, DH, Reserved14, Reserved15,
          CL, CH, Reserved16, Reserved17, AL, AH: Byte);
  end;

{ Date and time record used by PackTime and UnpackTime }

  DateTime = record
               Year,
               Month,
               Day,
               Hour,
               Min,
               Sec: word;
             end;


const
  { Error code value ( 0 - no error ) }
  DosError: integer = 0;

{ DosVersion returns dos version number like BP DosVersion }
function DosVersion: word;

{ Intr simulate a real mode interrupt }
procedure Intr(IntNo: byte; var regs: registers);

{MsDos call DOS interrupt 21h }
procedure MsDos(var regs: registers);

{ Date and Time routines }
procedure GetDate(var Year,Month,Day,DayOfWeek: word);
procedure SetDate(Year,Month,Day: word);
procedure GetTime(var Hour,Minute,Second,Sec100: word);
procedure SetTime(Hour,Minute,Second,Sec100: word);

{ Get or Set Ctrl-Break Status }
procedure GetCBreak( var BreakStatus: boolean);
procedure SetCBreak( BreakStatus: boolean);

procedure GetVerify(var Verify: boolean);
procedure SetVerify(Verify: boolean);

{ Returns the number of available bytes on the Drive }
function DiskFree(Drive: Byte): Longint;

{ Return the size in bytes of the specified drive }
function DiskSize(Drive: Byte): Longint;


{ GetFAttr returns the attributes of a file. }

procedure GetFAttr(var F; var Attr: Word);

{ SetFAttr sets the attributes of a file. }

procedure SetFAttr(var F; Attr: Word);

{ GetFTime returns the date and time a file was last written.   }

procedure GetFTime(var F; var Time: Longint);

{ SetFTime sets the date and time a file was last written.      }

procedure SetFTime(var F; Time: Longint);

{ FindFirst searches the specified (or current) directory for }
{ the first entry that matches the specified filename and }
{ attributes. }

procedure FindFirst( const Path: PathStr; Attr: Word; var F: SearchRec);

{ FindNext returs the next entry that matches the name and }
{ attributes specified in a previous call to FindFirst. The }
{ search record must be one passed to FindFirst. }

procedure FindNext(var F: SearchRec);

{ UnpackTime converts a 4-byte packed date/time returned by }
{ FindFirst, FindNext or GetFTime into a DateTime record. }

procedure UnpackTime(P: Longint; var T: DateTime);

{ PackTime converts a DateTime record into a 4-byte packed }
{ date/time used by SetFTime. }

procedure PackTime(var T: DateTime; var P: Longint);

{ GetIntVec returns the address stored in the specified }
{ interrupt vector. }
{
procedure GetIntVec(IntNo: Byte; var Vector: Pointer);

{ SetIntVec sets the address in the interrupt vector table for }
{ the specified interrupt. }

procedure SetIntVec(IntNo: Byte; Vector: Pointer);
}
{ FSearch searches for the file given by Path in the list of    }
{ directories given by DirList. The directory paths in DirList  }
{ must be separated by semicolons. The search always starts     }
{ with the current directory of the current drive. The returned }
{ value is a concatenation of one of the directory paths and    }
{ the file name, or an empty string if the file could not be    }
{ located.                                                      }

function FSearch(const Path: PathStr; const DirList: String): PathStr;

{ FExpand expands the file name in Path into a fully qualified  }
{ file name. The resulting name consists of a drive letter, a   }
{ colon, a root relative directory path, and a file name.       }
{ Embedded '.' and '..' directory references are removed.       }

function FExpand( const Path: PathStr): PathStr;

{ FSplit splits the file name specified by Path into its three  }
{ components. Dir is set to the drive and directory path with   }
{ any leading and trailing backslashes, Name is set to the file }
{ name, and Ext is set to the extension with a preceding dot.   }
{ Each of the component strings may possibly be empty, if Path  }
{ contains no such component.                                   }

procedure FSplit( const Path: PathStr; var Dir: DirStr;
  var Name: NameStr; var Ext: ExtStr);

{ EnvCount returns the number of strings contained in the DOS   }
{ environment.                                                  }

function EnvCount: Integer;

{ EnvStr returns a specified environment string. The returned   }
{ string is of the form "VAR=VALUE". The index of the first     }
{ string is one. If Index is less than one or greater than      }
{ EnvCount, EnvStr returns an empty string.                     }

function EnvStr(Index: Integer): String;

{ EnvName returns a specified environment variable name. }
{ The index of the first string is one. If Index is less than one }
{ or greater than EnvCount, EnvStr returns an empty string. }

function EnvName(Index: Integer): String;

{ GetEnv returns the value of a specified environment variable. }
{ This routine is case sensitive. The result dos not include '=' }
{ character. If the specified environment variable does not }
{ exist, GetEnv returns an empty string. }

function GetEnv( const EnvVar: String): String;

{ SwapVectors swaps the contents of the SaveIntXX pointers in   }
{ the System unit with the current contents of the interrupt    }
{ vectors. SwapVectors is typically called just before and just }
{ after a call to Exec. This insures that the Exec'd process    }
{ does not use any interrupt handlers installed by the current  }
{ process, and vice versa.                                      }

procedure SwapVectors;

{ Keep (or Terminate Stay Resident) terminates the program and  }
{ makes it stay in memory. The entire program stays in memory,  }
{ including data segment, stack segment, and heap. The ExitCode }
{ corresponds to the one passed to the Halt standard procedure. }
{
procedure Keep(ExitCode: Word);
}
{ Exec executes another program. The program is specified by    }
{ the Path parameter, and the command line is specified by the  }
{ CmdLine parameter. To execute a DOS internal command, run     }
{ COMMAND.COM, e.g. "Exec('\COMMAND.COM','/C DIR *.PAS');".     }
{ Note the /C in front of the command. Errors are reported in   }
{ DosError. When compiling a program that uses Exec, be sure    }
{ to specify a maximum heap size as there will otherwise not be }
{ enough memory.                                                }

procedure Exec( const Path: PathStr; const ComLine: ComStr);

{ DosExitCode returns the exit code of a sub-process. The low   }
{ byte is the code sent by the terminating process. The high    }
{ byte is zero for normal termination, 1 if terminated by       }
{ Ctrl-C, 2 if terminated due to a device error, or 3 if        }
{ terminated by the Keep procedure (function call 31 hex).      }

function DosExitCode: Word;


implementation

function DosVersion: word; assembler;
asm
   mov ah, $30
   int $21
end;


procedure Intr(IntNo: byte; var regs: registers); assembler;
asm
   mov   eax, $0300
   movzx ebx, byte ptr [IntNo]
   mov   edi, dword ptr [Regs]
   xor   ecx, ecx
   int   $31
end;

procedure MsDos(var regs: registers); assembler;
asm
   mov   eax, $0300
   mov   ebx, $21
   mov   edi, dword ptr [Regs]
   xor   ecx, ecx
   int   $31
end;

procedure GetDate(var Year,Month,Day,DayOfWeek: word); assembler;
asm
   mov   ah, $2A
   int   $21
   xor   ah, ah
   mov   ebx, dword ptr [DayOfWeek]
   mov   word ptr [ebx], ax
   mov   ebx, dword ptr [Day]
   mov   al, dl
   mov   word ptr [ebx], ax
   mov   ebx, dword ptr [Month]
   mov   al, dh
   mov   word ptr [ebx], ax
   mov   ebx, dword ptr [Year]
   mov   word ptr [ebx], cx
end;

procedure SetDate(Year, Month, Day: word); assembler;
asm
   mov   cx, Year
   sub   cx, 1980
   mov   dl, byte ptr [ Day]
   mov   dh, byte ptr [ Month]
   mov   ah, $2B
   int   $21
   movzx eax, al
   mov   word ptr [DosError], ax
end;

procedure GetTime(var Hour,Minute,Second,Sec100: word); assembler;
asm
   mov     ah, $2C
   int     $21
   lea     eax, [Hour]
   ror     ecx, 8
   sub     ch, ch
   mov     word ptr [eax], cx
   lea     eax, [Minute]
   rol     ecx, 8
   sub     ch, ch
   mov     word ptr [eax], cx
   lea     eax, [Second]
   ror     edx, 8
   sub     dh, dh
   mov     word ptr [eax], dx
   lea     eax, [Sec100]
   rol     edx, 8
   sub     dh, dh
   mov     word ptr [eax], dx
end;

procedure SetTime(Hour,Minute,Second,Sec100: word); assembler;
asm
   mov   ch, byte ptr [Hour]
   mov   cl, byte ptr [Minute]
   mov   dh, byte ptr [Second]
   mov   dl, byte ptr [Sec100]
   mov   ah, $21
   int   $21
   movzx eax, al
   mov   word ptr [DosError], ax
end;

procedure GetCBreak(var BreakStatus: boolean); assembler;
asm
   mov   eax, $3300
   int   $21
   mov   edi, dword ptr [BreakStatus]
   mov   byte ptr [edi], dl
end;

procedure SetCBreak(BreakStatus: boolean); assembler;
asm
   mov   eax, $3301
   mov   dl, byte ptr [BreakStatus]
   int   $21
end;

procedure GetVerify(var Verify: boolean); assembler;
asm
   mov   ah, $54
   int   $21
   mov   edi, dword ptr [Verify]
   mov   byte ptr [edi], al
end;

procedure SetVerify(Verify: boolean); assembler;
asm
   mov   ah, $2e
   mov   al, byte ptr [Verify]
   xor   edx, edx
   int   $21
end;

function DiskFree(Drive: byte): longint; assembler;
asm
   mov   ah, $36
   mov   dl, byte ptr [Drive]
   xor   ebx, ebx
   xor   ecx, ecx
   int   $21
   movzx eax, ax
   cmp   ax, $FFFF
   jne   @ok
   mov   word ptr [DosError], ax
@ok:
   mul   ecx
   mul   ebx
end;

function DiskSize(Drive: byte): longint; assembler;
asm
   push  ds
   xor   edx, edx
   mov   dl, byte ptr [Drive]
   xor   ecx, ecx
   mov   ah, $1C
   int   $21
   pop   ds
   movzx eax, al
   cmp   al, $ff
   jnz   @ok
   mov   word ptr [DosError],ax
@ok:
   mul   edx
   mul   ecx
end;


procedure GetFAttr(var F; var Attr: Word); assembler;
  asm
    mov edx, dword ptr [ F]
    lea edx, [edx].TextRec.Name
    mov eax, $4300
    int $21
    jc  @@error
    xor ax, ax
    jmp @@return
  @@error:
    xor cx, cx
  @@return:
    mov DosError, ax
    mov edi, dword ptr [ Attr]
    mov word ptr [edi], cx
  end;


procedure SetFAttr(var F; Attr: Word); assembler;
  asm
    mov edx, dword ptr [ F]
    lea edx, [edx].FileRec.Name
    mov eax, $4301
    mov cx, Attr
    int $21
    jc  @@error
    xor ax, ax
  @@error:
    mov DosError, ax
  end;


procedure GetFTime(var F; var Time: Longint); assembler;
  asm
    mov edx, dword ptr [ F]
    mov bx, [edx].FileRec.Handle
    mov eax, $5700
    int $21
    jnc @@ok
    xor cx, cx
    xor dx, dx
    jmp @@return
  @@ok:
    xor ax, ax
  @@return:
    mov DosError, ax
    mov edi, dword ptr [ Time]
    mov word ptr [ edi], cx
    mov word ptr [ edi + 2], dx
  end;


procedure SetFTime(var F; Time: Longint); assembler;
  asm
    mov edx, dword ptr [ F]
    mov bx, [ edx].FileRec.Handle
    mov eax, $5701
    mov cx, word ptr [ Time]
    mov dx, word ptr [ Time + 2]
    int $21
    jc  @@error
    xor ax, ax
  @@error:
    mov DosError, ax
  end;


procedure Find_NameConvert( var F: SearchRec); assembler;
  asm
    jc  @@error
    mov edi, dword ptr [ F]
    lea edi, [ edi].SearchRec.Name
    cld
    xor al, al
    mov ecx, 256
    repne scasb
    not cl
    mov al, cl
    dec edi
    mov esi, edi
    dec esi
    std
    rep movsb
    stosb
    cld
    xor ax, ax
  @@error:
    mov DosError, ax
  end;


procedure FindFirst( const Path: PathStr; Attr: Word; var F: SearchRec); assembler;
  var
    Buf: array [0..79] of char;
  asm
    lea edi, Buf
    mov esi, dword ptr [ Path]
    cld
    lodsb
    cmp al, 79
    jbe @@1
    mov al, 79
  @@1:
    movzx ecx, al
    jcxz @@end_loop
    rep movsb
  @@end_loop:
    xor al, al
    stosb

    mov eax, $1A00
    mov edx, dword ptr [ F]
    int $21
    mov eax, $4E00
    lea edx, Buf
    mov cx, Attr
    int $21

    push dword ptr [ F]
    call Find_NameConvert
  end;


procedure FindNext(var F: SearchRec); assembler;
  asm
    mov eax, $1A00
    mov edx, dword ptr [ F]
    int $21
    mov eax, $4F00
    int $21
    push dword ptr [ F]
    call Find_NameConvert
  end;


procedure UnpackTime(P: Longint; var T: DateTime); assembler;
  asm
    mov edi, dword ptr [ T]
    mov ecx, P
    mov eax, ecx
    shr eax, 25
    add eax, 1980
    stosw
    and ecx, $01FFFFFF
    mov eax, ecx
    shr eax, 21
    stosw
    and ecx, $001FFFFF
    mov eax, ecx
    shr eax, 16
    stosw
    mov ax, cx
    shr ax, 11
    stosw
    and cx, $07FF
    mov ax, cx
    shr ax, 5
    stosw
    and cx, $001F
    mov ax, cx
    shl ax, 1
    stosw
  end;


procedure PackTime(var T: DateTime; var P: Longint); assembler;
  asm
    mov esi, dword ptr [ T]
    lodsw
    sub ax, 1980
    movzx ecx, ax
    shl ecx, 4
    lodsw
    and ax, $000F
    or  cx, ax
    shl ecx, 5
    lodsw
    and ax, $001F
    or  cx, ax
    shl ecx, 5
    lodsw
    and ax, $001F
    or  cx, ax
    shl ecx, 6
    lodsw
    and ax, $003F
    or  cx, ax
    shl ecx, 5
    lodsw
    shr ax, 1
    and ax, $001F
    or  cx, ax
    mov edi, dword ptr [ P]
    mov dword ptr [edi], ecx
  end;

{
procedure GetIntVec(IntNo: Byte; var Vector: Pointer); assembler;
  asm
  end;


procedure SetIntVec(IntNo: Byte; Vector: Pointer); assembler;
  asm
  end;
}

function FSearch( const Path: PathStr; const DirList: String): PathStr; assembler;
  asm
    cld
    mov esi, dword ptr [ DirList]
    lodsb
    movzx ebx, al
    add ebx, esi
    mov edi, dword ptr [ @Result]
    inc edi

  @@loop:
    push esi
    mov esi, dword ptr [ Path]
    lodsb
    movzx ecx, al
    rep movsb
    xor al, al
    stosb
    dec edi

    mov edx, dword ptr [ @Result]
    inc edx
    mov eax, $4300
    int $21
    {cmp esp, l
    jne @@exit}
    pop esi
    jc  @@NotFound
    test cx, $18
    je  @@Exit

  @@NotFound:
    mov edi, dword ptr [ @Result]
    inc edi
    cmp esi, ebx
    je  @@Exit
    xor ax, ax
  @@copydir:
    lodsb
    cmp al, ';'
    je  @@endcopy
    stosb
    mov ah, al
    cmp esi, ebx
    jne @@copydir

  @@endcopy:
    cmp ah, ':'
    je  @@loop
    cmp ah, '\'
    je  @@loop
    mov al, '\'
    stosb
    jmp @@loop

  @@Exit:
    mov eax, edi
    mov edi, dword ptr [ @Result]
    sub eax, edi
    dec al
    stosb
  end;


function FExpand( const Path: PathStr): PathStr; assembler;
  asm
    mov esi, dword ptr [ Path]
    mov edi, dword ptr [ @Result]
    lodsb
    inc edi
    movzx ecx, al
    add ecx, esi
    lodsw
    cmp esi, ecx
    ja  @@GetDrive
    cmp ah, ':'
    jne @@GetDrive
    cmp al, 'a'
    jb  @@1
    cmp al, 'z'
    ja  @@1
    sub al, $20
    jmp @@1

  @@GetDrive:
    dec esi
    dec esi
    mov ax, $1900
    int $21
    add al, 'A'
    mov ah, ':'

  @@1:
    stosw
    cmp esi, ecx
    je  @@GetCurDir
    cmp byte ptr [ esi], '\'
    je  @@2

  @@GetCurDir:
    push esi
    sub al, 'A' - 1
    mov dl, al
    mov al, '\'
    stosb
    mov esi, edi
    mov ax, $4700
    int $21
    pop esi
    jc  @@2

    push ecx
    mov ecx, -1
    xor al, al
    repne scasb
    pop ecx
    dec edi
    cmp byte ptr [ edi - 1], '\'
    je  @@2
    mov al, '\'
    stosb

  @@2:
    sub ecx, esi
    rep movsb
    xor al, al
    stosb

    mov esi, dword ptr [ @Result]
    inc esi
    mov edi, esi
    push edi

  @@loop:
    lodsb
    or  al, al
    je  @@EOL
    cmp al, '\'
    je  @@Slash
    cmp al, 'a'
    jb  @@3
    cmp al, 'z'
    ja  @@3
    sub al, $20
  @@3:
    stosb
    jmp @@loop

  @@Slash:
  @@EOL:
    cmp word ptr [ edi - 2], '.' * 256 + '\'
    jne @@4
    dec edi
    dec edi
    jmp @@6

  @@4:
    cmp word ptr [ edi - 2], '.' * 256 + '.'
    jne @@6
    cmp byte ptr [ edi - 3], '\'
    jne @@6
    sub edi, 3
    cmp byte ptr [ edi - 1], ':'
    je  @@6
  @@5:
    dec edi
    cmp byte ptr [ edi], '\'
    jne @@5
  @@6:
    or  al, al
    jne @@3
    cmp byte ptr [ edi - 1], ':'
    jne @@7
    mov al, '\'
    stosb
  @@7:
    mov eax, edi
    pop edi
    sub eax, edi
    dec edi
    stosb
  end;


procedure FSplit( const Path: PathStr; var Dir: DirStr;
  var Name: NameStr; var Ext: ExtStr); assembler;
  asm
    mov esi, dword ptr [ Path]
    movzx ecx, byte ptr [ esi]
    add esi, ecx
    std
    xor edx, edx
    jcxz @@1

  @@Loop:
    lodsb
    cmp al, '\'
    je  @@1
    cmp al, ':'
    je  @@1
    inc edx
    loop @@Loop
    dec esi

  @@1:
    mov ecx, edx
    inc esi
    push esi
    inc esi
    mov edi, dword ptr [ Name]
    inc edi
    mov edx, edi
    cld
    xor ebx, ebx

  @@2:
    jcxz @@4
    lodsb
    cmp al, '.'
    jne  @@21
    dec esi
    jmp @@4
  @@21:
    cmp ebx, 8
    jae @@3
    stosb
    inc ebx
  @@3:
    dec ecx
    jmp @@2

  @@4:
    mov eax, edi
    sub eax, edx
    mov edi, edx
    dec edi
    stosb

    mov edi, dword ptr [ Ext]
    cmp ecx, 4
    jbe @@5
    mov ecx, 4
  @@5:
    mov al, cl
    stosb
    jcxz @@6
    rep movsb

  @@6:
    mov esi, dword ptr [ Path]
    pop eax
    sub eax, esi
    inc esi
    mov edi, dword ptr [ Dir]
    stosb
    mov ecx, eax
    jcxz @@7
    rep movsb
  @@7:
  end;


function EnvCount: Integer; assembler;
  asm
    mov esi, EnvironmentBlock
    xor eax, eax

  @@Loop:
    cmp dword ptr [esi], 0
    je  @@Exit
    inc eax
    add esi, 4
    jmp @@Loop

  @@Exit:
  end;


function EnvName(Index: Integer): String; assembler;
  asm
    mov esi, dword ptr [ EnvironmentBlock]
    mov edi, dword ptr [ @Result]
    movzx ecx, Index
    dec ecx

  @@Loop:
    lodsd
    or  eax, eax
    je  @@Empty
    jcxz @@Found
    dec ecx
    jmp @@Loop

  @@Empty:
    xor al, al
    stosb
    jmp @@Exit

  @@Found:
    mov esi, eax
    mov edx, edi
    inc edi
    xor ecx, ecx

  @@Copy:
    lodsb
    or  al, al
    je  @@EndCopy
    cmp al, '='
    je  @@EndCopy
    stosb
    inc ecx
    cmp ecx, 255
    jne @@Copy

  @@EndCopy:
    mov al, cl
    mov edi, edx
    stosb

  @@Exit:
  end;

function EnvStr(Index: Integer): String; assembler;
  asm
    mov esi, dword ptr [ EnvironmentBlock]
    mov edi, dword ptr [ @Result]
    movzx ecx, Index
    dec ecx

  @@Loop:
    lodsd
    or  eax, eax
    je  @@Empty
    jcxz @@Found
    dec ecx
    jmp @@Loop

  @@Empty:
    xor al, al
    stosb
    jmp @@Exit

  @@Found:
    mov esi, eax
    mov edx, edi
    inc edi
    xor ecx, ecx

  @@Copy:
    lodsb
    or  al, al
    je  @@EndCopy
    stosb
    inc ecx
    cmp ecx, 255
    jne @@Copy

  @@EndCopy:
    mov al, cl
    mov edi, edx
    stosb

  @@Exit:
  end;


function GetEnv( const EnvVar: String): String; assembler;
  asm
    mov esi, EnvironmentBlock

  @@SearchLoop:
    lodsd
    or  eax, eax
    je  @@NotFound
    push esi
    mov esi, dword ptr [ EnvVar]
    mov edi, eax
    lodsb
    movzx ecx, al
    repe cmpsb
    jne @@1
    or  ecx, ecx
    jne @@1
    cmp byte ptr [ edi], '='
    je  @@Found
  @@1:
    pop esi
    jmp @@SearchLoop

  @@Found:
    mov esi, edi
    inc esi
    mov edi, dword ptr [@Result]
    mov edx, edi
    inc edi
    xor ecx, ecx

  @@Copy:
    lodsb
    or  al, al
    je  @@EndCopy
    cmp al, '='
    je  @@EndCopy
    stosb
    inc ecx
    cmp ecx, 255
    jne @@Copy

  @@EndCopy:
    mov al, cl
    mov edi, edx
    stosb
    jmp @@Exit

  @@NotFound:
    mov edi, dword ptr [@Result]
    xor al, al
    stosb

  @@Exit:
  end;


procedure SwapVectors; assembler;
  asm
    mov eax, $0202
    mov bl, 0
    int $31
    xchg edx, dword ptr [ SaveInt00]
    xchg cx, word ptr [ SaveInt00 + 4]
    mov eax, $0203
    mov bl, 0
    int $31

    mov eax, $0202
    mov bl, $0C
    int $31
    xchg edx, dword ptr [ SaveInt0C]
    xchg cx, word ptr [ SaveInt0C + 4]
    mov eax, $0203
    mov bl, $0C
    int $31

    mov eax, $0202
    mov bl, $0D
    int $31
    xchg edx, dword ptr [ SaveInt0D]
    xchg cx, word ptr [ SaveInt0D + 4]
    mov eax, $0203
    mov bl, $0D
    int $31

    mov eax, $0200
    mov bl, $1B
    int $31
    xchg dx, word ptr [ SaveInt1B]
    xchg cx, word ptr [ SaveInt1B + 2]
    mov eax, $0201
    mov bl, $1B
    int $31

    mov eax, $0200
    mov bl, $23
    int $31
    xchg dx, word ptr [ SaveInt23]
    xchg cx, word ptr [ SaveInt23 + 2]
    mov eax, $0201
    mov bl, $23
    int $31

    mov eax, $0204
    mov bl, $21
    int $31
    xchg edx, dword ptr [ SaveInt21]
    xchg cx, word ptr [ SaveInt21 + 4]
    mov eax, $0205
    mov bl, $21
    int $31
  end;

{
procedure Keep(ExitCode: Word); assembler;
  asm
  end;
}

type
  tExecParBlock = record
    EnvOffset: LongInt;
    EnvSel: Word;
    CmdOffset: LongInt;
    CmdSel: Word;
  end;

procedure Exec( const Path: PathStr; const ComLine: ComStr); assembler;
  var
    ParBlk: tExecParBlock;
    P, C: array [0..127] of char;
  asm
    mov esi, dword ptr [ Path]
    cld
    lodsb
    movzx ecx, al
    lea edi, P
    jcxz @@1
    rep movsb
  @@1:
    xor al, al
    stosb

    mov esi, dword ptr [ ComLine]
    lea edi, C
    lodsb
    movzx ecx, al
    add al, 2
    stosb
    jcxz @@2
    rep movsb
  @@2:
    mov al, 13
    stosb
    xor al, al
    stosb

    lea ebx, ParBlk
    lea eax, C
    mov [ebx].tExecParBlock.CmdOffset, eax
    mov [ebx].tExecParBlock.CmdSel, ds

    push ds
    mov ds, PrefixSeg
    mov ax, word ptr ds:[ $2C]
    pop ds
    mov [ebx].tExecParBlock.EnvOffset, 0
    mov [ebx].tExecParBlock.EnvSel, ax

    lea edx, P
    mov eax, $4B00
    int $21
    jc  @@3
    xor ax, ax
  @@3:
    mov DosError, ax
  end;

  {type
    pParamBlock = ^tParamBlock;
    tparamblock = record
      EnvSeg: Word;
      CmdTailOfs: Word;
      CmdTailSeg: Word;
      FCB1Ofs: Word;
      FCB1Seg: Word;
      FCB2Ofs: Word;
      FCB2Seg: Word;
      Res1, Res2: Pointer;
    end;
  var
    CurPos: LongInt;

  procedure ConcatStr( Seg: Word; var Pos: LongInt; const Str: String);
    var
      S: String;
    begin
      {S := Str;
      writeln( S, Pos: 10);}
      {S[Length(S)+1] := #0;}
      asm
        mov esi, dword ptr [ &Str]
        mov edi, Pos
        mov edi, dword ptr [edi]
        push es
        mov es, &Seg
        lodsb
        movzx ecx, al
        jcxz @@1
        rep movsb
      @@1:
        xor al, al
        stosb
        pop es
        mov edx, dword ptr [Pos]
        mov dword ptr [edx], edi
      end;
      {Move( S[1], Ptr( Seg, Pos)^, Length(S) + 1);}
      {Inc( Pos, Length(S) + 1);}
    end;

  var
    r: record
      _edi, _esi, _ebp, r1, _ebx, _edx, _ecx, _eax: longint;
      _flags, _es, _ds, _fs, _gs, _ip, _cs, _sp, _ss: word;
    end;
    seg1, seg2, sel1, sel2: word;
    FCB1, FCB2, env, po, co: word;
    memseg, memsel: word;
    pbl: pParamBlock;
    i: Integer;
    res: boolean;
    s: string;
  begin
    move( comline[0], s[1], length( comline) + 1);
    s[ length( comline) + 2] := #13;
    s[ 0] := chr( length( comline) + 2);
    res := true;
    asm
      mov eax, $0100
      mov bx, 1024
      int $31
      jnc @@ok
      mov res, 0
    @@ok:
      mov memseg, ax
      mov memsel, dx
    end;
    if not res then exit;
    CurPos := 0;
    env := 0;
    Inc( CurPos, Env);
    for i := 1 to EnvCount() do
      ConcatStr( MemSel, CurPos, EnvStr( i));
    ConcatStr( MemSel, CurPos, '');
    co := CurPos;
    ConcatStr( MemSel, CurPos, Path);
    po := CurPos;
    ConcatStr( MemSel, CurPos, s);
    FCB1 := CurPos;
    Inc( CurPos, 32);
    FCB2 := CurPOs;
    Inc( CurPos, 32);
    pbl := Pointer( CurPos);
    r._es := MemSeg;
    r._ds := MemSeg;
    r._edi := Fcb1;
    r._esi := PO;
    r._eax := $2901;
    asm
      push es
      push ss
      pop es
      lea edi, r
      mov eax, $0300
      mov bx, $21
      xor cx, cx
      int $31
      pop es
    end;

    r._es := MemSeg;
    r._ds := MemSeg;
    r._edi := Fcb2;
    r._esi := PO;
    r._eax := $2901;
    asm
      push es
      push ss
      pop es
      lea edi, r
      mov eax, $0300
      mov bx, $21
      xor cx, cx
      int $31
      pop es
    end;

    asm
      mov edi, pbl
      push es
      mov es, MemSel
      mov ax, MemSeg
      mov es:[edi].tParamBlock.EnvSeg, ax
      mov es:[edi].tParamBlock.CmdTailSeg, ax
      mov ax, po
      mov es:[edi].tParamBlock.CmdTailOfs, ax
      pop es
    end;

    asm
      mov edi, pbl
      push es
      mov es, MemSel
      mov ax, MemSeg
      mov es:[edi].tParamBlock.FCB1seg, ax
      mov es:[edi].tParamBlock.FCB2seg, ax
      mov ax, FCB1
      mov es:[edi].tParamBlock.FCB1ofs, ax
      mov ax, FCB2
      mov es:[edi].tParamBlock.FCB2ofs, ax
      pop es
    end;
    r._eax := $4b00;
    r._ds := MemSeg;
    r._es := MemSeg;
    r._edx := co;
    r._ebx := CurPos;
    asm
      push es
      push ss
      pop es
      lea edi, r
      mov eax, $0300
      mov bl, $21
      xor bh, bh
      xor ecx, ecx
      int $31
      pop es
    end;
    writeln( r._eax);
  end;}



function DosExitCode: Word; assembler;
  asm
    mov eax, $4D00
    int $21
  end;


begin
end.
