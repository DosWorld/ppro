
procedure SetLoad( Dest, Source: Pointer; Min, Max: LongInt); assembler; 'setload';
  asm
    mov edi, dword ptr [Dest]
    mov esi, dword ptr [Source]

    mov ecx, Min  { Обнулить начало }
    shr ecx, 3
    mov edx, ecx
    jcxz @@1
    xor al, al
    rep stosb

  @@1:
    mov ecx, Max  { Скопировать данные }
    shr ecx, 3
    inc ecx
    mov ebx, ecx
    sub ecx, edx
    jcxz @@2
    rep movsb

  @@2:
    mov ecx, 32   { Обнулить конец }
    sub ecx, ebx
    jcxz @@3
    rep stosb

  @@3:
    mov edi, dword ptr [Dest]  { Обнулить начало первого байта }
    mov al, $FF
    mov ecx, Min
    and ecx, 7
    shl al, cl
    and byte ptr [edi + edx], al

    mov al, $FF                { Обнулить конец последнего байта }
    mov ecx, Max
    {inc ecx}
    not ecx
    and ecx, 7
    {inc ecx}
    shr al, cl
    and byte ptr [edi + ebx - 1], al
  end;

procedure SetStore( Source, Dest: Pointer; Min, Max: LongInt); assembler; 'setstore';
  asm
    mov edi, dword ptr [Dest]
    mov esi, dword ptr [Source]

    mov edx, Min   { Скопировать данные }
    shr edx, 3
    add esi, edx
    mov ecx, Max
    shr ecx, 3
    inc ecx
    sub ecx, edx
    mov ebx, ecx
    jbe @@1
    rep movsb

  @@1:
    mov edi, dword ptr [Dest]  { Обнулить начало первого байта }
    mov al, $FF
    mov ecx, Min
    and ecx, 7
    shl al, cl
    and byte ptr [edi], al

    mov al, $FF                { Обнулить конец последнего байта }
    mov ecx, Max
    inc ecx
    not ecx
    and ecx, 7
    inc ecx
    and ecx, 7
    shr al, cl
    and byte ptr [edi + ebx - 1], al
  end;

procedure SetSetItem( Dest: Pointer; Item: LongInt); assembler; 'setsetitem';
  asm
    mov edi, dword ptr [Dest]
    movzx eax, byte ptr [ Item]
    {cmp eax, 255
    ja @@exit}
    mov ebx, eax
    shr ebx, 3
    and eax, 7
    xor edx, edx
    mov dl, byte ptr [edi+ebx]
    bts dx, ax
    mov byte ptr [edi+ebx], dl
  @@exit:
  end;

procedure SetSetRange( Dest: Pointer; First, Last: LongInt); assembler; 'setsetrange';
  asm
    mov edi, dword ptr [Dest]
    mov ecx, Last
    mov eax, First
    sub ecx, eax
    inc ecx
    jcxz @@exit
    cmp eax, 255
    ja @@exit
    mov ebx, eax
    shr ebx, 3
    and eax, 7
    xor edx, edx

  @@loop:
    mov dl, byte ptr [edi+ebx]

  @@1:
    bts dx, ax
    inc ax
    and ax, 7
    jz @@2
    loop @@1
  @@2:
    mov byte ptr [edi+ebx], dl
    jcxz @@exit
    inc ebx
    loop  @@loop

  @@exit:
  end;

procedure SetUnion( Dest, Source: Pointer); assembler; 'setunion';
  asm
    mov edi, dword ptr [Dest]
    mov esi, dword ptr [Source]
    mov ecx, 8
  @@loop:
    lodsd
    or dword ptr [edi], eax
    add edi, 4
    loop @@loop
  end;

procedure SetDifference( Dest, Source: Pointer); assembler; 'setdifference';
  asm
    mov edi, dword ptr [Dest]
    mov esi, dword ptr [Source]
    mov ecx, 8
  @@loop:
    lodsd
    not eax
    and dword ptr [edi], eax
    add edi, 4
    loop @@loop
  end;

procedure SetIntersect( Dest, Source: Pointer); assembler; 'setintersect';
  asm
    mov edi, dword ptr [Dest]
    mov esi, dword ptr [Source]
    mov ecx, 8
  @@loop:
    lodsd
    and dword ptr [edi], eax
    add edi, 4
    loop @@loop
  end;

function SetIn( P: Pointer; Item: LongInt): Boolean; assembler; 'setin';
  asm
    mov edi, dword ptr [P]
    mov ecx, Item
    mov ebx, ecx
    and ecx, 7
    shr ebx, 3
    xor eax, eax
    mov al, byte ptr [edi + ebx]
    bt  ax, cx
    setc al
  end;

function SetEqual( P1, P2: Pointer): Boolean; assembler; 'setequal';
  asm
    mov edi, dword ptr [P1]
    mov esi, dword ptr [P2]
    mov ecx, 8
    rep cmpsd
    setz al
  end;

function SetCompare( P1, P2: Pointer): Boolean; assembler; 'setcompare';
  asm
    mov edi, dword ptr [P1]
    mov esi, dword ptr [P2]
    mov ecx, 8
  @@loop:
    lodsd
    or eax, dword ptr [edi]
    scasd
    jnz  @@1
    loop @@loop
  @@1:
    setz al
  end;


procedure SetInclude( Dest: Pointer; Item, Min, Max: LongInt); assembler; 'setinclude';
  asm
    mov edi, dword ptr [Dest]
    mov eax, Item
    cmp eax, Max
    ja @@exit
    cmp eax, Min
    jb @@exit
    mov ebx, eax
    shr ebx, 3
    mov edx, min
    shr edx, 3
    sub ebx, edx
    and eax, 7
    xor edx, edx
    mov dl, byte ptr [edi+ebx]
    bts dx, ax
    mov byte ptr [edi+ebx], dl
  @@exit:
  end;

procedure SetExclude( Dest: Pointer; Item, Min, Max: LongInt); assembler; 'setexclude';
  asm
    mov edi, dword ptr [Dest]
    mov eax, Item
    cmp eax, Max
    ja @@exit
    cmp eax, Min
    jb @@exit
    mov ebx, eax
    shr ebx, 3
    mov edx, min
    shr edx, 3
    sub ebx, edx
    and eax, 7
    xor edx, edx
    mov dl, byte ptr [edi+ebx]
    btr dx, ax
    mov byte ptr [edi+ebx], dl
  @@exit:
  end;

