{                    GNU LESSER GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Full text of license:
 https://www.gnu.org/licenses/lgpl-3.0.en.html

 (c) Copyright 2022 DosWord
 (c) Copyright 1997-1998 Iggor Khachko - hachko@icl.kazan.su }

unit Strings;

interface

{ StrLen returns the number of characters in Str, not counting  }
{ the null terminator.                                          }

function StrLen(Str: pChar): LongInt;

{ StrEnd returns a pointer to the null character that           }
{ terminates Str.                                               }

function StrEnd(Str: pChar): pChar;

{ StrMove copies exactly Count characters from Source to Dest   }
{ and returns Dest. Source and Dest may overlap.                }

function StrMove(Dest, Source: pChar; Count: LongInt): pChar;

{ StrCopy copies Source to Dest and returns Dest.               }

function StrCopy(Dest, Source: pChar): pChar;

{ StrECopy copies Source to Dest and returns StrEnd(Dest).      }

function StrECopy(Dest, Source: pChar): pChar;

{ StrLCopy copies at most MaxLen characters from Source to Dest }
{ and returns Dest.                                             }

function StrLCopy(Dest, Source: pChar; MaxLen: LongInt): pChar;

{ StrPCopy copies the Pascal style string Source into Dest and  }
{ returns Dest.                                                 }

function StrPCopy(Dest: pChar; const Source: String): pChar;

{ StrCat appends a copy of Source to the end of Dest and        }
{ returns Dest.                                                 }

function StrCat(Dest, Source: pChar): pChar;

{ StrLCat appends at most MaxLen - StrLen(Dest) characters from }
{ Source to the end of Dest, and returns Dest.                  }

function StrLCat(Dest, Source: pChar; MaxLen: LongInt): pChar;

{ StrComp compares Str1 to Str2. The return value is less than  }
{ 0 if Str1 < Str2, 0 if Str1 = Str2, or greater than 0 if      }
{ Str1 > Str2.                                                  }

function StrComp(Str1, Str2: pChar): LongInt;

{ StrIComp compares Str1 to Str2, without case sensitivity. The }
{ return value is the same as StrComp.                          }

function StrIComp(Str1, Str2: pChar): LongInt;

{ StrLComp compares Str1 to Str2, for a maximum length of       }
{ MaxLen characters. The return value is the same as StrComp.   }

function StrLComp(Str1, Str2: pChar; MaxLen: LongInt): LongInt;

{ StrLIComp compares Str1 to Str2, for a maximum length of      }
{ MaxLen characters, without case sensitivity. The return value }
{ is the same as StrComp.                                       }

function StrLIComp(Str1, Str2: pChar; MaxLen: LongInt): LongInt;

{ StrScan returns a pointer to the first occurrence of Chr in   }
{ Str. If Chr does not occur in Str, StrScan returns NIL. The   }
{ null terminator is considered to be part of the string.       }

function StrScan(Str: pChar; Chr: Char): pChar;

{ StrRScan returns a pointer to the last occurrence of Chr in   }
{ Str. If Chr does not occur in Str, StrRScan returns NIL. The  }
{ null terminator is considered to be part of the string.       }

function StrRScan(Str: pChar; Chr: Char): pChar;

{ StrPos returns a pointer to the first occurrence of Str2 in   }
{ Str1. If Str2 does not occur in Str1, StrPos returns NIL.     }

function StrPos(Str1, Str2: pChar): pChar;

{ StrUpper converts Str to upper case and returns Str.          }

function StrUpper(Str: pChar): pChar;

{ StrLower converts Str to lower case and returns Str.          }

function StrLower(Str: pChar): pChar;

{ StrPas converts Str to a Pascal style string.                 }

function StrPas(Str: pChar): String;

{ StrNew allocates a copy of Str on the heap. If Str is NIL or  }
{ points to an empty string, StrNew returns NIL and doesn't     }
{ allocate any heap space. Otherwise, StrNew makes a duplicate  }
{ of Str, obtaining space with a call to the GetMem standard    }
{ procedure, and returns a pointer to the duplicated string.    }
{ The allocated space is StrLen(Str) + 1 bytes long.            }

function StrNew(Str: pChar): pChar;

{ StrDispose disposes a string that was previously allocated    }
{ with StrNew. If Str is NIL, StrDispose does nothing.          }

procedure StrDispose(Str: pChar);

implementation


function StrLen(Str: pChar): LongInt; assembler;
  asm
    mov edi, dword ptr [ &Str]
    mov edx, edi
    xor eax, eax
    mov ecx, eax
    dec ecx
    cld
    repne scasb
    dec edi
    mov eax, edi
    sub eax, edx
  end;


function StrEnd(Str: pChar): pChar; assembler;
  asm
    mov edi, dword ptr [ &Str]
    mov edx, edi
    xor eax, eax
    mov ecx, eax
    dec ecx
    cld
    repne scasb
    mov eax, edi
    dec eax
  end;


function StrMove(Dest, Source: pChar; Count: LongInt): pChar; assembler;
  asm
    mov esi, Source
    mov edi, Dest
    mov ecx, Count
    mov eax, edi
    cld
    cmp esi, edi
    jae @@DoCopy
    std
    add esi, ecx
    add edi, ecx
    dec esi
    dec edi
  @@DoCopy:
    rep movsb
    cld
  end;


function StrCopy(Dest, Source: pChar): pChar; assembler;
  asm
    mov edi, Source
    xor eax, eax
    mov ecx, eax
    dec ecx
    cld
    repne scasb
    not ecx
    mov esi, Source
    mov edi, Dest
    mov eax, edi
    rep movsb
  end;


function StrECopy(Dest, Source: pChar): pChar; assembler;
  asm
    mov edi, Source
    xor eax, eax
    mov ecx, eax
    dec ecx
    cld
    repne scasb
    not ecx
    mov esi, Source
    mov edi, Dest
    rep movsb
    mov eax, edi
    dec eax
  end;


function StrLCopy(Dest, Source: pChar; MaxLen: LongInt): pChar; assembler;
  asm
    mov edi, Source
    xor eax, eax
    mov ecx, MaxLen
    mov edx, ecx
    cld
    repne scasb
    sub edx, ecx
    mov ecx, edx
    mov esi, Source
    mov edi, Dest
    mov edx, edi
    rep movsb
    stosb
    mov eax, edx
  end;


function StrPCopy(Dest: pChar; const Source: String): pChar; assembler;
  asm
    mov esi, dword ptr [ Source]
    mov edi, Dest
    cld
    lodsb
    movzx ecx, al
    mov edx, edi
    rep movsb
    xor al, al
    stosb
    mov eax, edx
  end;


function StrCat(Dest, Source: pChar): pChar; assembler;
  asm
    push dword ptr [ Dest]
    call StrEnd
    push eax
    push dword ptr [ Source]
    call StrCopy
    mov eax, Dest
  end;


function StrLCat(Dest, Source: pChar; MaxLen: LongInt): pChar; assembler;
  asm
    push dword ptr [ Dest]
    call StrEnd
    mov ecx, Dest
    add ecx, MaxLen
    sub ecx, eax
    jbe @@Exit
    push eax
    push dword ptr [ Source]
    push ecx
    call StrLCopy

  @@Exit:
    mov eax, Dest
  end;


function StrComp(Str1, Str2: pChar): LongInt; assembler;
  asm
    mov esi, Str1
    mov edi, esi
    xor eax, eax
    mov ecx, eax
    dec ecx
    cld
    repne scasb
    not ecx
    mov edi, Str2
    repe cmpsb
    movzx eax, byte ptr [ esi - 1]
    movzx edx, byte ptr [ edi - 1]
    sub eax, edx
  end;


function StrIComp(Str1, Str2: pChar): LongInt; assembler;
  asm
    mov esi, Str1
    mov edi, esi
    xor eax, eax
    mov ecx, eax
    dec ecx
    cld
    repne scasb
    not ecx
    mov edi, Str2

  @@Loop:
    repe cmpsb
    je  @@Exit
    movzx eax, byte ptr [ esi - 1]
    cmp al, 'a'
    jb  @@1
    cmp al, 'z'
    ja  @@1
    sub al, $20
  @@1:
    movzx edx, byte ptr [ edi - 1]
    cmp dl, 'a'
    jb  @@2
    cmp dl, 'z'
    ja  @@2
    sub dl, $20
  @@2:
    sub eax, edx
    je  @@Loop

  @@Exit:
  end;


function StrLComp(Str1, Str2: pChar; MaxLen: LongInt): LongInt; assembler;
  asm
    mov eax, MaxLen
    mov ecx, eax
    jcxz @@Exit
    mov edx, eax
    mov esi, Str1
    mov edi, esi
    xor eax, eax
    cld
    repne scasb
    sub edx, ecx
    mov ecx, edx
    mov edi, Str2
    repe cmpsb
    movzx eax, byte ptr [ esi - 1]
    movzx edx, byte ptr [ edi - 1]
    sub eax, edx
  @@Exit:
  end;


function StrLIComp(Str1, Str2: pChar; MaxLen: LongInt): LongInt; assembler;
  asm
    mov eax, MaxLen
    mov ecx, eax
    jcxz @@Exit
    mov edx, eax
    mov esi, Str1
    mov edi, esi
    xor eax, eax
    cld
    repne scasb
    sub edx, ecx
    mov ecx, edx
    mov edi, Str2

  @@Loop:
    repe cmpsb
    je  @@Exit
    movzx eax, byte ptr [ esi - 1]
    cmp al, 'a'
    jb  @@1
    cmp al, 'z'
    ja  @@1
    sub al, $20
  @@1:
    movzx edx, byte ptr [ edi - 1]
    cmp dl, 'a'
    jb  @@2
    cmp dl, 'z'
    ja  @@2
    sub dl, $20
  @@2:
    sub eax, edx
    je  @@Loop

  @@Exit:
  end;


function StrScan(Str: pChar; Chr: Char): pChar; assembler;
  asm
    mov edi, &Str
    mov edx, edi
    xor eax, eax
    mov ecx, eax
    dec ecx
    cld
    repne scasb
    not ecx
    mov edi, edx
    mov al, Chr
    repne scasb
    mov eax, edi
    dec eax
  end;


function StrRScan(Str: pChar; Chr: Char): pChar; assembler;
  asm
    mov edi, &Str
    xor eax, eax
    mov ecx, eax
    dec ecx
    cld
    repne scasb
    not ecx
    dec edi
    mov al, Chr
    std
    repne scasb
    cld
    mov eax, edi
    inc eax
  end;


function StrPos(Str1, Str2: pChar): pChar; assembler;
  asm
    mov esi, Str2
    mov edi, esi
    cld
    xor eax, eax
    mov ecx, eax
    dec ecx
    repne scasb
    not ecx
    dec ecx
    jz  @@Unequal
    mov edx, ecx
    mov edi, Str1
    mov ebx, edi
    mov ecx, eax
    dec ecx
    repne scasb
    not ecx
    sub ecx, edx
    jbe @@Unequal
    mov edi, ebx

  @@Loop:
    mov esi, Str2
    lodsb
    repne scasb
    jne @@Unequal
    mov ebx, ecx
    mov eax, edi
    mov ecx, edx
    dec ecx
    repe cmpsb
    mov ecx, ebx
    mov edi, eax
    jne @@Loop
    dec eax
    jmp @@Exit

  @@Unequal:
    xor eax, eax

  @@Exit:
  end;


function StrUpper(Str: pChar): pChar; assembler;
  asm
    mov esi, &Str
    mov ebx, esi
    cld

  @@Loop:
    lodsb
    or  al, al
    jz  @@Exit
    cmp al, 'a'
    jb  @@Loop
    cmp al, 'z'
    ja  @@Loop
    sub al, $20
    mov byte ptr [ esi - 1], al
    jmp @@Loop

  @@Exit:
    mov eax, ebx
  end;


function StrLower(Str: pChar): pChar; assembler;
  asm
    mov esi, &Str
    mov ebx, esi
    cld

  @@Loop:
    lodsb
    or  al, al
    jz  @@Exit
    cmp al, 'A'
    jb  @@Loop
    cmp al, 'Z'
    ja  @@Loop
    add al, $20
    mov byte ptr [ esi - 1], al
    jmp @@Loop

  @@Exit:
    mov eax, ebx
  end;


function StrPas(Str: pChar): String; assembler;
  asm
    mov esi, &Str
    mov edi, esi
    xor eax, eax
    mov ecx, eax
    dec ecx
    cld
    repne scasb
    not ecx
    dec ecx
    cmp ecx, 255
    jbe @@1
    mov ecx, 255
  @@1:
    mov edi, dword ptr [ @Result]
    mov al, cl
    stosb
    rep movsb
  end;


function StrNew(Str: pChar): pChar;
  var
    L: LongInt;
  begin
    L := StrLen( Str);
    if L > 0 then
      begin
        GetMem( Result, L + 1);
        StrCopy( Result, Str);
      end
    else
      Result := nil;
  end;


procedure StrDispose(Str: pChar);
  begin
    if Assigned( Str) then
      FreeMem( Str, StrLen( Str) + 1);
  end;


end.