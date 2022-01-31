{                    GNU GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Full text of license:
 https://www.gnu.org/licenses/gpl-3.0.en.html

 (c) Copyright 2022 DosWord
 (c) Copyright 1997-1998 Iggor Khachko - hachko@icl.kazan.su }

{$IFDEF TP}
{$X+,V-,G+,N+,E-,B-,T-}
{$IFDEF DEBUG}
{$I+,S+,R+,C+}
{$ELSE}
{$I-,S-,R-,C-}
{$ENDIF}
{$ENDIF}

unit AsmOpt;

interface

uses Objects, IAsm386;

type

  pAsmCode = ^tAsmCode;
  tAsmCode = record
    Instruction: pAsmInstruction;
    Next: pAsmCode;
  end;

  pProcAsm = ^tProcAsm;
  tProcAsm = object( tObject)
    First: pAsmCode;
    Last: pAsmCode;
    TempSize: LongInt;
    destructor Done; virtual;
    procedure Insert( Instr: pAsmInstruction);
    procedure Concat( Instr: pAsmInstruction);
    procedure WriteTo( S: pStream);
  end;

procedure OptomizeAsm( var First, Last: pAsmCode);
function UsedRegister( Reg: tRegister; First, Last: pAsmCode): Boolean;

implementation

{ tProcAsm }
destructor tProcAsm.Done;
  var
    AsmCode: pAsmCode;
  begin
    while Assigned( First) do
      begin
        AsmCode := First;
        First := First^.Next;
        Dispose( AsmCode^.Instruction, Done);
        Dispose( AsmCode);
      end;
  end;

procedure tProcAsm.Insert( Instr: pAsmInstruction);
  var
    AsmCode: pAsmCode;
  begin
    New( AsmCode);
    AsmCode^.Instruction := Instr;
    AsmCode^.Next := First;
    First := AsmCode;
    if not Assigned( Last) then
      Last := First;
  end;

procedure tProcAsm.Concat( Instr: pAsmInstruction);
  begin
    if Assigned( Last) then
      begin
        New( Last^.Next);
        Last := Last^.Next;
      end
    else
      begin
        New( Last);
        First := Last;
      end;
    Last^.Next := nil;
    Last^.Instruction := Instr;
  end;

procedure tProcAsm.WriteTo( S: pStream);
  var
    Cur: pAsmCode;
  begin
    Cur := First;
    while Assigned( Cur) do
      begin
        if Assigned( Cur^.Instruction) then
          Cur^.Instruction^.WriteTo( S);
        Cur := Cur^.Next;
      end;
  end;

{*****}
procedure PackCode( var First, Last: pAsmCode);
  var
    P: ^pAsmCode;
    Next: pAsmCode;
  begin
    if Assigned( First) and Assigned( Last) then
      begin
        P := @First;
        while (P^ <> Last^.Next) and Assigned( P^) do
          begin
            Next := P^^.Next;
            if Assigned( P^^.Instruction) then
              begin
                case P^^.Instruction^.OpCode of
                  caiLEA:
                    with P^^.Instruction^ do
                    begin
                      if (Op1.Location = clRegister) and
                        (Op2.Location = clMemory) and
                        (Op3.Location = clNone) then
                        begin
                          if (Op2.Reference.Index = crNoRegister) and
                            Assigned( Op2.Reference.Symbol) and
                            (Op2.Reference.Base = Op1.Register) then
                            if (Op2.Reference.Offset = 0) then
                              begin
                                Dispose( P^^.Instruction, Done);
                                Dispose( P^);
                                P^ := Next;
                                continue;
                              end
                            else
                              begin
                                OpCode := caiADD;
                                Op2.Location := clImmediate;
                                Op2.Value := Op2.Reference.Offset;
                              end
                        end;
                    end;
                  caiJMP:
                    if Assigned( Next) and
                      (P^^.Instruction^.Op1.Location = clOffset) and
                      Assigned( Next^.Instruction) and
                      Assigned( Next^.Instruction^.LabelName) and
                      (P^^.Instruction^.Op1.LabelName^ = Next^.Instruction^.LabelName^) then
                      begin
                        Dispose( P^^.Instruction, Done);
                        Dispose( P^);
                        P^ := Next;
                        continue;
                      end;
                end;
              end;
            P := @P^^.Next;
          end;
      end;
  end;


{*****}
procedure DoFirstOptomize( var First, Last: pAsmCode);
  var
    P: ^pAsmCode;
    p1, p2, p3: pAsmCode;
    i1, i2, i3: pAsmInstruction;
  begin
    if Assigned( First) and Assigned( Last) then
      begin
        P := @First;
        while (P^ <> Last^.Next) and Assigned( P^) do
          begin
            p1 := P^;
            if Assigned( p1) then
              p2 := p1^.Next
            else 
              break;
            if Assigned( p2) then
              p3 := p2^.Next
            else
              break;
            i1 := p1^.Instruction;
            i2 := p2^.Instruction;
            {i3 := p3^.Instruction;}
            if Assigned( P^^.Instruction) then
              begin
                case i1^.OpCode of
                  caiMOV:
                    begin
                      if i2^.OpCode = caiMOV then
                        begin
                          if (i1^.Op1.Location = clRegister) and
                            (i1^.Op2.Location = clMemory) and
                            (i2^.Op1.Location = clMemory) and
                            (i2^.Op2.Location = clRegister) and
                            (i1^.Op1.Register = i2^.Op2.Register) and
                            EqualReferences(i1^.Op2.Reference, i2^.Op1.Reference) then
                            begin
                              Dispose( p2^.Instruction, Done);
                              Dispose( p2);
                              p1^.Next := p2;
                              continue;
                            end;
                        end;
                    end;
                  caiLEA:
                    begin
                      if (i2^.Op1.Location = clMemory) then
                        begin
                          if (i2^.Op1.Reference.Base = i1^.Op1.Register) and
                            not ((i1^.Op2.Reference.Index <> crNoRegister) and
                              (i2^.Op1.Reference.Index <> crNoRegister)) then
                            begin
                              {i2^.Op1.Reference.Base := i1^.Op2.Reference.Base;
                              if i1^.Op2.Reference.Index <> crNoRegister then
                                i2^.Op1.Reference.Index := i1^.Op2.Reference.Index;
                              Inc( i2^.Op1.Reference.Offset, i1^.Op2.Reference.Offset);
                              if Assigned( i1^.Op2.Reference.Symbol) then
                                i2^.Op1.Reference.Symbol := NewStr( i1^.Op2.Reference.Symbol^);
                              if not UsedRegister( i1^.Op1.Register, p3, Last) then
                                begin
                                  Dispose( p1^.Instruction, Done);
                                  Dispose( p1);
                                  P^ := p2;
                                  continue;
                                end;}
                            end;
                        end
                      else if (i2^.Op2.Location = clMemory) then
                        begin
                          if (i2^.Op2.Reference.Base = i1^.Op1.Register) and
                            not ((i1^.Op2.Reference.Index <> crNoRegister) and
                            (i2^.Op2.Reference.Index <> crNoRegister)) then
                            begin
                              {i2^.Op2.Reference.Base := i1^.Op2.Reference.Base;
                              if i1^.Op2.Reference.Index <> crNoRegister then
                                begin
                                  i2^.Op2.Reference.Index := i1^.Op2.Reference.Index;
                                  i2^.Op2.Reference.Scale := i1^.Op2.Reference.Scale;
                                end;
                              Inc( i2^.Op2.Reference.Offset, i1^.Op2.Reference.Offset);
                              if Assigned( i1^.Op2.Reference.Symbol) then
                                i2^.Op2.Reference.Symbol := NewStr( i1^.Op2.Reference.Symbol^);
                              if not UsedRegister( i1^.Op1.Register, p2, Last) then
                                begin
                                  Dispose( p1^.Instruction, Done);
                                  Dispose( p1);
                                  P^ := p2;
                                  continue;
                                end;}
                            end;
                        end;
                    end;
                end;
              end;
            P := @P^^.Next;
          end;
      end;
  end;


{ OptomizeAsm }

procedure OptomizeAsm( var First, Last: pAsmCode);
  begin
    PackCode( First, Last);
    DoFirstOptomize( First, Last);
    PackCode( First, Last);
  end;

function UsedRegister( Reg: tRegister; First, Last: pAsmCode): Boolean;
  var
    P: pAsmCode;
  begin
    UsedRegister := False;
    p := First;
    while Assigned( p) and (p <> Last^.Next) do
      begin
        if Assigned( p^.Instruction) then
          with p^.Instruction^ do
            begin
              case Op2.Location of
                clMemory:
                  if (Op2.Reference.Base = Reg) or (Op2.Reference.Index = Reg) then
                    begin
                      UsedRegister := True;
                      Exit;
                    end;
                clRegister:
                  if Op2.Register = Reg then
                    if ((OpCode = caiXOR) or (OpCode = caiSUB)) and
                      (Op1.Location = clRegister) and
                      (Op1.Register = Reg) then
                      Exit
                    else
                      begin
                        UsedRegister := True;
                        Exit;
                      end;
              end;
              case Op3.Location of
                clMemory:
                  if (Op3.Reference.Base = Reg) or (Op3.Reference.Index = Reg) then
                    begin
                      UsedRegister := True;
                      Exit;
                    end;
                clRegister:
                  if Op3.Register = Reg then
                    begin
                      UsedRegister := True;
                      Exit;
                    end;
              end;
              case Op1.Location of
                clMemory:
                  if (Op1.Reference.Base = Reg) or (Op1.Reference.Index = Reg) then
                    begin
                      UsedRegister := True;
                      Exit;
                    end;
                clRegister:
                  if Op1.Register = Reg then
                    if (OpCode = caiMOV) or (OpCode = caiLEA) or
                      (OpCode = caiPOP) or (OpCode = caiMOVSX) or
                      (OpCode = caiMOVZX) then
                      Exit
                    else
                      begin
                        UsedRegister := True;
                        Exit;
                      end;
              end;
            end;
        p := p^.Next;
      end;
  end;

end.