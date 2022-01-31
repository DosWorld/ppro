{                    GNU LESSER GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Full text of license:
 https://www.gnu.org/licenses/lgpl-3.0.en.html

 (c) Copyright 2022 DosWord
 (c) Copyright 1997-1998 Iggor Khachko - hachko@icl.kazan.su }

procedure InsertFreeBlock( Block: Pointer); assembler;
  asm
    mov ebx, Block

    or  ebx, ebx
    jz  @@exit

    mov ecx, dword ptr [ebx + 4]
    lea eax, [ebx + ecx]
    cmp eax, HeapPtr
    jae @@free
    mov ecx, HeapPtr
    lea esi, [FreeList]
    mov edi, FreeList

  @@loop:
    or  edi, edi
    jz  @@concat
    cmp ebx, edi
    ja  @@insert
    mov ecx, esi
    mov esi, edi
    mov edi, dword ptr [esi]
    jmp @@loop

  @@free:
    mov HeapPtr, ebx
    mov edi, FreeList
    mov eax, dword ptr [edi + 4]
    lea eax, [edi + eax]
    cmp eax, ebx
    jne @@exit
    mov HeapPtr, edi
    mov edi, dword ptr [edi]
    mov FreeList, edi
    jmp @@exit

  @@insert:
    cmp eax, esi
    jne @@1
    mov dword ptr [ecx], ebx
    mov eax, dword ptr [esi + 4]
    add eax, dword ptr [ebx + 4]
    mov dword ptr [ebx + 4], eax
    mov esi, ecx
    jmp @@2
  @@1:
    mov dword ptr [esi], ebx
  @@2:
    mov dword ptr [ebx], edi
    mov ecx, dword ptr [edi + 4]
    lea eax, [edi + ecx]
    cmp eax, ebx
    jne @@exit
    add ecx, dword ptr [ebx + 4]
    mov dword ptr [edi + 4], ecx
    mov dword ptr [esi], edi
    jmp @@exit

  @@concat:
    mov dword ptr [esi], ebx
    mov dword ptr [ebx], edi

  @@exit:
    mov esi, FreeList
    or  esi, esi
    je  @@Ret
    mov eax, dword ptr [ esi + 4]
    lea eax, [ esi + eax]
    cmp eax, HeapPtr
    jne @@Ret
    mov HeapPtr, esi
    mov eax, dword ptr [esi]
    mov FreeList, eax
    jmp @@Exit
  @@Ret:
  end;

function HeapErrorHandler( Size: LongInt): LongInt; assembler;
  asm
    xor eax, eax
  end;

procedure GetMem( var P: Pointer; Size: LongInt); assembler; 'new';
  asm
    mov ecx, Size
    or ecx, ecx
    jz @@exit
    add ecx, 7
    and ecx, $FFFFFFF8

  @@Retry:
    lea ebx, [FreeList]
    mov edx, FreeList

  @@loop:
    or  edx, edx
    jz  @@ptr

    mov eax, dword ptr [edx + 4]
    cmp eax, ecx
    jge @@found
    mov ebx, edx
    mov edx, dword ptr [ebx]
    jmp @@loop

  @@found:
    or  edx, edx
    jz  @@ptr
    mov esi, dword ptr [edx]
    cmp eax, ecx
    je  @@1
    lea edi, [edx + ecx]
    sub eax, ecx
    mov dword ptr [edi], esi
    mov dword ptr [edi + 4], eax
    mov esi, edi
  @@1:
    mov dword ptr [ebx], esi
    jmp @@exit

  @@ptr:
    mov edx, HeapPtr
    mov eax, HeapEnd
    sub eax, edx
    cmp eax, ecx
    jge  @@greater
    jz  @@equal

    mov ebx, HeapError
    or  ebx, ebx
    jz  @@error
    call dword ptr [HeapError]
    or  eax, eax
    jz  @@error
    dec eax
    jnz @@Retry
    xor edx, edx
    jmp @@exit

  @@error:
    push HeapOverflow
    call RunError

  @@greater:
    {lea edi, [edx + ecx]
    mov esi, FreeList
    mov dword ptr [edi], esi
    sub eax, ecx
    mov dword ptr [edi + 4], eax}
  @@equal:
    lea edi, [edx + ecx]
    mov HeapPtr, edi
    jmp @@exit

  @@exit:
    mov edi, dword ptr [P]
    mov dword ptr [edi], edx
  end;

procedure FreeMem( var P: Pointer; Size: LongInt); assembler; 'dispose';
  asm
    mov edx, P
    mov edx, dword ptr [edx]
    or  edx, edx
    jz  @@error
    cmp edx, HeapOrg
    jb  @@error
    mov ecx, Size
    add ecx, 7
    and ecx, $FFFFFFF8
    jz  @@exit
    mov eax, edx
    add eax, ecx
    cmp eax, HeapPtr
    ja  @@error

    mov dword ptr [edx], 0
    mov dword ptr [edx + 4], ecx
    push edx
    call InsertFreeBlock
    {mov esi, HeapPtr
    lea edi, [edx + ecx]
    cmp edi, esi
    je  @@1
    mov edi, FreeList
    mov dword ptr [edx], edi
    mov dword ptr [edx + 4], ecx
    mov FreeList, edx}
    jmp @@exit

  @@1:
    mov HeapPtr, edx
    jmp @@exit

  @@error:
    push InvalidPointerOperation
    call RunError

  @@exit:
  end;

procedure InitHeap; assembler;
  var
    MemInfo: array [0..11] of LongInt;
  asm
    mov ax, $EE42
    mov edx, HeapSize
    int $31
    test eax, eax
    jz @@error
    mov HeapOrg, edx
    mov HeapPtr, edx
    add edx, eax
    mov HeapEnd, edx
    mov FreeList, 0
    mov HeapError, HeapErrorHandler
    jmp @@exit

    {{mov ax, $0500
    lea edi, MemInfo
    int $31

    jc  @@error}

    {mov cx, word ptr [MemInfo]
    mov bx, word ptr [MemInfo + 2]}
    mov cx, HeapSizeLo
    mov bx, HeapSizeHi
    mov ax, $0501
    int $31
    jc  @@error
    mov word ptr [HeapHandle], di
    mov word ptr [HeapHandle + 2], si
    mov word ptr [HeapOrg], cx
    mov word ptr [HeapOrg + 2], bx

    mov ax, $0006
    mov bx, ds
    int $31
    jc  @@error
    sub word ptr [HeapOrg], dx
    sbb word ptr [HeapOrg + 2], cx

    mov eax, HeapOrg
    mov HeapPtr, eax
    {add eax, dword ptr [MemInfo]}
    add eax, HeapSizeLo + HeapSizeHi * $10000
    mov HeapEnd, eax
    mov FreeList, 0
    mov HeapError, HeapErrorHandler
    jmp @@exit}

  @@error:
    mov  eax, ErrorAllocatingHeap
    push eax
    call RunError

  @@exit:
  end;

function MemAvail: LongInt; assembler;
  asm
    xor eax, eax
    mov edx, FreeList

  @@loop:
    or  edx, edx
    jz  @@1
    add eax, dword ptr [edx + 4]
    mov edx, dword ptr [edx]
    jmp @@loop

  @@1:
    mov edx, HeapEnd
    sub edx, HeapPtr
    add eax, edx
  end;

function MaxAvail: LongInt; assembler;
  asm
    xor eax, eax
    mov edx, FreeList

  @@loop:
    or  edx, edx
    jz  @@1
    mov ecx, dword ptr [edx + 4]
    cmp ecx, eax
    jbe @@0
    mov eax, ecx
  @@0:
    mov edx, dword ptr [edx]
    jmp @@loop

  @@1:
    mov edx, HeapEnd
    sub edx, HeapPtr
    cmp edx, eax
    jbe @@exit
    mov eax, edx
  @@exit:
  end;

const
  HeapErrorMessage: String = 'Ошибка при освобождении памяти';
procedure DoneHeap; assembler;
  asm 
    mov eax, $EE40
    int $31

  @@exit:
    mov HeapOrg, 0
    mov HeapPtr, 0
    mov HeapEnd, 0
    mov HeapHandle, 0
  end;
