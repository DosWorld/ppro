{-----------------------------------------------------------------------}
{    Pascal Pro                                                         }
{       CG_Flat unit                                                    }
{                                              (c) Copyright 1997-1998  }
{                                   Iggor Khachko - hachko@icl.kazan.su }
{-----------------------------------------------------------------------}

{
  Code generator for flat memory model.
}

{$IFDEF TP}
{$X+,V-,G+,N+,E-,B-,T-}
{$IFDEF DEBUG}
{$I+,S+,R+,C+}
{$ELSE}
{$I-,S-,R-,C-}
{$ENDIF}
{$ENDIF}

unit CG_Flat;

interface

uses Objects, Tools, IAsm386, Symbols, AsmOpt, AsmCode, Code;

type

  pFlatCodeGenerator = ^tFlatCodeGenerator;
  tFlatCodeGenerator = object( tCodeGenerator)

    procedure GetReference( CodeTree: pCodeTree; Register: tRegister;
      var Ref: tReference); virtual;

  end;


function GenerateFlatCode( CodeTree: pCodeTree; aLexLevel: Byte;
  aLocalSize: LongInt): pProcAsm;

implementation


procedure tFlatCodeGenerator.GetReference( CodeTree: pCodeTree; Register: tRegister; var Ref: tReference);
  var
    Code: pCodeTree;
    Offset: LongInt;
    Reference: tReference;

  procedure CreateReference( CodeTree: pCodeTree; BaseReg: tRegister; var Ref: tReference);
    var
      LevelDif: Integer;
    begin
        case CodeTree^.Node.Symbol^.VarType of
          cvtGlobal:
            begin
              IAsm386.CreateReference( crDefaultSeg, crNoRegister, crNoRegister,
                1, 0, NewStr(CodeTree^.Node.Symbol^.AsmName),
                csDefault, Ref);
              Res^.Concat( _LEA_( BaseReg, Ref));
              Ref.Base := BaseReg;
              Ref.Symbol := nil;
              Ref.Size := GetSize( CodeTree^.ResType^.GetSize);
            end;
          cvtLocal,
          cvtParam:
            begin
              IAsm386.CreateReference( crDefaultSeg, crEBP, crNoRegister,
                1, 0, nil, csDefault, Ref);
              {Ref.Symbol := nil;
              Ref.Segment := crDefaultSeg;
              Ref.Base := crEBP;
              Ref.Index := crNoRegister;
              Ref.Scale := 1;}
              LevelDif := LexLevel - pFunctionDefinition(CodeTree^.Node.Symbol^.Owner^.Owner)^.LexLevel;
              if LevelDif = 0 then
                begin
                  Ref.Offset := CodeTree^.Node.Symbol^.Offset;
                  Res^.Concat( _LEA_( BaseReg, Ref));
                  Ref.Offset := 0;
                  Ref.Base := BaseReg;
                end
              else
                begin
                  while LevelDif > 0 do
                    begin
                      {UseRegister( crEDI);}
                      Ref.Size := csDWord;
                      Ref.Offset := 8;
                      Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
                        caiMOV, BaseReg, Ref)));
                      Ref.Symbol := nil;
                      Ref.Segment := crSS;
                      Ref.Base := BaseReg;
                      Ref.Index := crNoRegister;
                      Ref.Scale := 1;
                      Dec( LevelDif);
                    end;
                  if CodeTree^.Node.Symbol^.Offset <> 0 then
                    Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                      caiADD, BaseReg, CodeTree^.Node.Symbol^.Offset)));
                  Ref.Offset := 0;
                end;
              Ref.Scale := 1;
              Ref.Size := GetSize( CodeTree^.ResType^.GetSize);
            end;
          cvtVarParam,
          cvtStringParam,
          cvtConstParam:
            begin
              Ref.Symbol := nil;
              Ref.Segment := crDefaultSeg;
              Ref.Base := crEBP;
              Ref.Index := crNoRegister;
              Ref.Scale := 1;
              LevelDif := LexLevel - pFunctionDefinition(CodeTree^.Node.Symbol^.Owner^.Owner)^.LexLevel;
              while LevelDif > 0 do
                begin
                  {UseRegister( crEDI);}
                  Ref.Size := csDWord;
                  Ref.Offset := 8;
                  Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
                    caiMOV, BaseReg, Ref)));
                  Ref.Symbol := nil;
                  Ref.Segment := crDefaultSeg;
                  Ref.Base := BaseReg;
                  Ref.Index := crNoRegister;
                  Ref.Scale := 1;
                  Dec( LevelDif);
                end;
              Ref.Scale := 1;
              Ref.Offset := CodeTree^.Node.Symbol^.Offset;
              Ref.Size := csDWord;
              Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
                caiMOV, BaseReg, Ref)));
              Ref.Base := BaseReg;
              Ref.Offset := 0;
              Ref.Index := crNoRegister;
              Ref.Segment := crDefaultSeg;
              Ref.Size := GetSize( CodeTree^.ResType^.GetSize);
              Ref.Symbol := nil;
            end;
        end;
    end;

  var
    ResReg: tRegister;
    IsPush: Boolean;

  begin
    case CodeTree^.Node.CodeType of
      cctVariable:
          begin
            CreateReference( CodeTree, Register, Ref);
          end;

      cctTypeConversion:
        GetReference( CodeTree^.Left, Register, Ref);

      cctDeref:
        begin
          {ResReg := GetRegister( Register);
          IsPush := False;
          if ResReg in UsedRegisters then
            begin
              Res^.Concat( New( pAsmInstruction, Create_Reg(
                caiPUSH, ResReg)));
              IsPush := True;
            end;
          UseRegister( ResReg);}
          CodeTree^.Left^.Location.Location := clRegister;
          CodeTree^.Left^.Location.Register := Register;
          DoExpression( CodeTree^.Left);
          IAsm386.CreateReference( crDefaultSeg, Register, crNoRegister,
            1, 0, nil, GetSize( CodeTree^.ResType^.GetSize), Ref);
          {if not IsPush then
            ReleaseRegister( ResReg);}
        end;

      cctLoadValue,
      cctFunctionCall:
        begin
          if CodeTree^.Right^.Node.CodeType <> cctIntConst then
              begin
                GetReference( CodeTree^.Left, Register, Ref);
                LockRegister( Register);
                ResReg := GetRegister( Register);
                UseRegister( ResReg, IsPush);
                CodeTree^.Right^.Location.Location := clRegister;
                CodeTree^.Right^.Location.Register := ResReg;
                DoExpression( CodeTree^.Right);
                Ref.Index := ResReg;
                Res^.Concat( _LEA_( Register, Ref));
                IAsm386.CreateReference( crDefaultSeg, Register, crNoRegister,
                  1, 0, nil, csDefault, Ref);
                {if (Ref.Base <> crNoRegister) then
                  begin
                    Ref.Index := ResReg;
                    Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
                      caiLEA, ResReg, Ref)));
                    if Ref.Base in UsedRegisters then
                      Res^.Concat( New( pAsmInstruction, Create_Reg(
                        caiPOP, Ref.Base)));
                    IAsm386.CreateReference( crDefaultSeg, ResReg, crNoRegister, 1, 0,
                      nil, csDefault, Ref);
                  end
                else 
                  Ref.Base := ResReg;}
                ReleaseRegister( ResReg, IsPush);
                UnlockRegister( Register);
              end
            else
              begin
                GetReference( CodeTree^.Left, Register, Ref);
                if CodeTree^.Right^.Node.IntValue <> 0 then
                  Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                    caiADD, Register, CodeTree^.Right^.Node.IntValue)));
                {Inc( Ref.Offset, CodeTree^.Right^.Node.IntValue);}
              end;
        end;

      cctWithSymbol:
        begin
          IAsm386.CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
            -LocalSize - 4 * CodeTree^.Node.IntValue, nil, csDWord, Reference);
          Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
            caiMOV, Register, Reference)));
          IAsm386.CreateReference( crDefaultSeg, Register, crNoRegister, 1,
            0, nil, csDefault, Ref);
          if CodeTree^.Left^.Node.CodeType <> cctIntConst then
            begin
              LockRegister( Register);
              ResReg := GetRegister( Register);
              UseRegister( ResReg, IsPush);
              CodeTree^.Left^.Location.Location := clRegister;
              CodeTree^.Left^.Location.Register := ResReg;
              DoExpression( CodeTree^.Left);
              Ref.Index := ResReg;
              Res^.Concat( _LEA_( Register, Ref));
              IAsm386.CreateReference( crDefaultSeg, Register, crNoRegister,
                1, 0, nil, csDefault, Ref);
              {Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                caiMOV, crESI, ResReg)));}
              ReleaseRegister( ResReg, IsPush);
              UnlockRegister( Register);
              {if (Ref.Base <> crNoRegister) then
                begin
                  Ref.Index := ResReg;
                  Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
                    caiLEA, ResReg, Ref)));
                  if Ref.Base in UsedRegisters then
                    Res^.Concat( New( pAsmInstruction, Create_Reg(
                      caiPOP, Ref.Base)));
                  IAsm386.CreateReference( crDefaultSeg, ResReg, crNoRegister, 1, 0,
                    nil, csDefault, Ref);
                end
              else
                Ref.Base := ResReg;}
            end
          else
            if CodeTree^.Left^.Node.IntValue <> 0 then
              Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                caiADD, Register, CodeTree^.Left^.Node.IntValue)));
        end;

      cctAssignment:
        begin
          CodeTree^.Location.Location := clRegister;
          CodeTree^.Location.Register := Register;
          DoExpression( CodeTree);
        end;

      cctMem:
        begin
          CodeTree^.Left^.Location.Location := clRegister;
          CodeTree^.Left^.Location.Register := Register;
          DoExpression( CodeTree^.Left);
          IAsm386.CreateReference( crDefaultSeg, Register, crNoRegister,
                1, 0, nil, csDefault, Ref);
        end;

    end;
    Ref.Size := GetSize( CodeTree^.ResType^.GetSize);
  end;


function GenerateFlatCode( CodeTree: pCodeTree; aLexLevel: Byte; aLocalSize: LongInt): pProcAsm;
  var
    CodeGenerator: tFlatCodeGenerator;
  begin
{$IFDEF EXTDEBUG}
writeln( 'generating asm code');
{$ENDIF}
    CodeGenerator.Init( aLexLevel, aLocalSize);
    CodeGenerator.GenerateAsm( CodeTree);
    GenerateFlatCode := CodeGenerator.Res;
    CodeGenerator.Done;
  end;


end.