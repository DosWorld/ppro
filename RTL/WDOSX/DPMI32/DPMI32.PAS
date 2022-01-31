{                    GNU LESSER GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Full text of license:
 https://www.gnu.org/licenses/lgpl-3.0.en.html

 (c) Copyright 2022 DosWord
 (c) Copyright 1997-1998 Iggor Khachko - hachko@icl.kazan.su }

unit DPMI32;

interface

type
  { Protected mode selector     }
  tPMSelector = Word;
  { Real mode selector          }
  tRMSegment = Word;
  { Protected mode offset       }
  tPMOffset = LongInt;
  { Real mode offset            }
  tRMOffset = Word;

{ Allocates LDT descriptors. If successful returns base selector in     }
{ other case returns 0. The base and limit of the returned descriptors  }
{ will be 0, and the type will be "data"                                }
function AllocateLdtDescriptors( Count: Word): tPMSelector;

{ Frees LDT descriptor. Only one descriptor freed per call. Any segment }
{ registers containing the freed selector are set to $0000              }
procedure FreeLdtDescriptor( Sel: tPMSelector);

{ Converst real mode segment to protected mode selector. }
function SegmentToDescriptor( Seg: tRMSegment): tPMSelector;

const
  DPMIError: Integer = 0;

implementation

function AllocateLdtDescriptors( Count: Word): tPMSelector; assembler;
  asm
    xor eax, eax
    movzx ecx, Count
    int $31
    jnc  @@NoError
    mov cx, ax
    xor eax, eax
    jmp @@Exit
  @@NoError:
    xor cx, cx
    movzx eax, ax
  @@Exit:
    mov DPMIError, cx
  end;


procedure FreeLdtDescriptor( Sel: tPMSelector); assembler;
  asm
    mov eax, $0001
    movzx ebx, Sel
    int $31
    jc  @@Exit
    xor ax, ax
  @@Exit:
    mov DPMIError, ax
  end;


end.