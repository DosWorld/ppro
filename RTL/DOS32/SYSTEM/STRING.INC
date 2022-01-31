{                    GNU LESSER GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Full text of license:
 https://www.gnu.org/licenses/lgpl-3.0.en.html

 (c) Copyright 2022 DosWord
 (c) Copyright 1997-1998 Iggor Khachko - hachko@icl.kazan.su }

operator +=(var a: string; const b: string) res: string; assembler;
  asm
      mov ebx, dword ptr [a]

      movzx ecx, byte ptr [ebx]
      mov edx, ecx
      lea edi, [ebx + ecx]

      movzx ecx, byte ptr [b]
      add edx, ecx
      test edx, $FFFFFF00
      jz @@3
      and edx, $FF
      inc edx
      sub ecx, edx
      mov edx, 255

    @@3:
      or cl, cl
      je @@1
      lea esi, [b + 1]
      rep movsb

    @@1:
      mov byte ptr [ebx], dl

      mov edi, dword ptr [res]
      mov esi, ebx
      movzx ecx, byte ptr [esi]
      inc ecx
      rep movsb
  end;

function Copy( const S: String; Pos, Len: Integer): String; assembler;
  asm
    mov esi, dword ptr [ S]
    mov edi, dword ptr [ @Result]
    cld
    lodsb
    movzx eax, al
    or  al, al
    jz  @@Empty
    movzx edx, word ptr [ Pos]
    dec edx
    cmp eax, edx
    jl  @@Empty
    cmp edx, 0
    jge @@0
    xor edx, edx
  @@0:
    add esi, edx
    sub eax, edx
    {inc eax}
    movzx ecx, Len
    cmp eax, ecx
    jg  @@1
    mov ecx, eax
  @@1:
    cmp ecx, 255
    jle @@2
    mov ecx, 255
  @@2:
    mov al, cl
    stosb
    rep movsb
    jmp @@Exit

  @@Empty:
    xor al, al
    stosb
    
  @@Exit:
  end;

procedure Insert( const SubStr: String; var S: String; Pos: Integer); assembler;
  asm
    mov edi, dword ptr [ S]
    mov esi, dword ptr [ SubStr]
    cld
    lodsb
    or al, al
    jz  @@Exit
    movzx ebx, al
    movzx edx, Pos
    movzx ecx, byte ptr [ edi]
    cmp edx, ecx
    jle @@1
    mov edx, ecx
    inc edx
  @@1:
    cmp edx, 255
    jg  @@Exit
    cmp edx, 0
    jg  @@2
    mov edx, 1

  @@2:
    sub ecx, edx
    jl  @@6
    add ebx, edx
    cmp ebx, 255
    jg  @@6
    inc ecx
    push esi
    push edi
    lea esi, [ edi + edx]
    lea edi, [ edi + ebx]
    add ebx, ecx
    sub ebx, 255
    jle @@3
    sub ecx, ebx
    inc ecx
  @@3:
    lea esi, [ esi + ecx - 1]
    lea edi, [ edi + ecx - 1]
    std
    rep movsb
    cld
    pop edi
    pop esi

  @@6:
    movzx ecx, al
    movzx eax, byte ptr [ edi]
    add eax, ecx
    cmp eax, 255
    jle @@7
    mov eax, 255
  @@7:
    mov byte ptr [ edi], al
    lea edi, [edi + edx]
    add edx, ecx
    sub edx, 255
    jle @@8
    sub ecx, edx
    inc ecx
  @@8:
    rep movsb

  @@Exit:
  end;

procedure StrCat( var Dest, Source: String; MaxLen: LongInt); 'strcat'; assembler;
  asm
    mov edi, dword ptr [Dest]
    mov esi, dword ptr [Source]
    movzx ebx, byte ptr [edi]
    cmp ebx, MaxLen
    jae @@exit
    movzx ecx, byte ptr [esi]
    jcxz @@exit
    add ecx, ebx
    cmp ecx, MaxLen
    jbe @@1
    mov ecx, MaxLen
  @@1:
    mov byte ptr [edi], cl
    sub ecx, ebx
    add edi, ebx
    inc edi
    inc esi
    cld
    rep movsb
  @@exit:
  end;

procedure StrCopy( var Dest, Source: String; MaxLen: LongInt); 'strcopy'; assembler;
  asm
    mov edi, dword ptr [Dest]
    mov esi, dword ptr [Source]
    movzx ecx, byte ptr [esi]
    cmp ecx, MaxLen
    jbe @@1
    mov ecx, MaxLen
  @@1:
    mov byte ptr [edi], cl
    jcxz @@exit
    inc edi
    inc esi
    cld
    rep movsb
  @@exit:
  end;

function StrCompare( var S1, S2: String): LongInt; 'strcompare'; assembler;
  asm
    mov edi, dword ptr [S1]
    mov esi, dword ptr [S2]
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
    rep cmpsb
    mov al, byte ptr [esi - 1]
    cmp byte ptr [edi - 1], al
    jb @@lower
    ja @@greater
  @@eq:
    cmp edx, ebx
    jb @@lower
    ja @@greater
    xor eax, eax
    jmp @@exit
  @@lower:
    mov eax, -1
    jmp @@exit
  @@greater:
    mov eax, 1
  @@exit:
  end;

procedure Delete( var S: String; Pos, Num: Byte); assembler;
  asm
    mov edi, dword ptr [S]
    movzx eax, byte ptr [edi]
    movzx edx, Pos
    or  edx, edx
    jz  @@exit
    dec edx
    sub eax, edx
    jle @@exit
    movzx ebx, Num
    or  ebx, ebx
    jz  @@exit
    sub eax, ebx
    jg @@1
    mov byte ptr [edi], dl
    jmp @@exit
  @@1:
    mov ecx, eax
    add eax, edx
    sub byte ptr [edi], bl
    lea edi, [edi + edx + 1]
    lea esi, [edi + ebx]
    cld
    rep movsb

  @@exit:
  end;

function Pos( const SubStr, S: String): LongInt; assembler;
  asm
    mov edi, dword ptr [S]
    mov esi, dword ptr [SubStr]
    movzx ecx, byte ptr [edi]
    jcxz @@not_found
    movzx edx, byte ptr [esi]
    or  edx, edx
    jz  @@not_found
    sub ecx, edx
    jl @@not_found
    inc ecx
    inc edi
    jcxz @@not_found

  @@loop:
    mov esi, dword ptr [SubStr]
    mov al, byte ptr [esi + 1]
    repne scasb
    jne @@not_found
    mov edx, edi
    mov ebx, ecx
    movzx ecx, byte ptr [esi]
    inc esi
    dec edi
    rep cmpsb
    jz  @@found
    mov ecx, ebx
    mov edi, edx
    jcxz @@not_found
    jmp @@loop

  @@not_found:
    xor eax, eax
{    mov eax, ecx
    mov edi, dword ptr [S]
    sub eax, edi
    neg eax}
    jmp @@exit

  @@found:
    mov eax, edx
    sub eax, dword ptr [S]
    dec eax

  @@exit:
  end;
  