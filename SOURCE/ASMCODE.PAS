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

unit AsmCode;

interface

uses Objects, IAsm386, Code, Symbols, AsmOpt;


type

  pLoopStack = ^tLoopStack;
  tLoopStack = record
    EndLabel: pString;
    ConditionLabel: pString;
    Next: pLoopStack;
  end;

  pCodeGenerator = ^tCodeGenerator;
  tCodeGenerator = object( tObject)
    Res: pProcAsm;
    LexLevel: Byte;
    UsedRegisters: tRegisterSet;
    LocalSize: LongInt;
    CurTempSize: LongInt;
    LoopStack: pLoopStack;
    ExitLabel: pString;
    Counter: LongInt;

    constructor Init( aLexLevel: Byte; aLocalSize: LongInt);
    destructor Done; virtual;

    procedure GenerateAsm( CodeTree: pCodeTree);
    procedure GenerateExpression( CodeTree: pCodeTree);
    procedure DoBlock( CodeTree: pCodeTree);
    procedure DoExpression( CodeTree: pCodeTree);

    procedure DoAddition( CodeTree: pCodeTree); virtual;
    procedure DoSubtraction( CodeTree: pCodeTree); virtual;
    procedure DoMultiplication( CodeTree: pCodeTree); virtual;
    procedure DoDiv( CodeTree: pCodeTree); virtual;
    procedure DoMod( CodeTree: pCodeTree); virtual;
    procedure DoDivision( CodeTree: pCodeTree); virtual;
    procedure DoVariable( CodeTree: pCodeTree); virtual;
    procedure DoAssignment( CodeTree: pCodeTree); virtual;
    procedure DoTypeConversion( CodeTree: pCodeTree); virtual;
    procedure DoLoadValue( CodeTree: pCodeTree); virtual;
    procedure DoDeref( CodeTree: pCodeTree); virtual;
    procedure DoFunctionCall( CodeTree: pCodeTree); virtual;
    procedure DoFunctionParam( CodeTree: pCodeTree; CallType: tCallType); virtual;
    procedure DoPushParam( CodeTree: pCodeTree); virtual;
    procedure DoLoadAddress( CodeTree: pCodeTree); virtual;
    procedure DoStringConst( CodeTree: pCodeTree); virtual;
    procedure DoPCharConst( CodeTree: pCodeTree); virtual;
    procedure DoSetConst( CodeTree: pCodeTree); virtual;
    procedure DoSetItem( CodeTree: pCodeTree); virtual;
    procedure DoSetRange( CodeTree: pCodeTree); virtual;
    procedure DoAnd( CodeTree: pCodeTree); virtual;
    procedure DoOr( CodeTree: pCodeTree); virtual;
    procedure DoXor( CodeTree: pCodeTree); virtual;
    procedure DoNot( CodeTree: pCodeTree); virtual;
    procedure DoNeg( CodeTree: pCodeTree); virtual;
    procedure DoShrShl( var CodeTree: pCodeTree; AC: tAsmOp); virtual;
    {procedure DoEqual( var CodeTree: pCodeTree); virtual;
    procedure DoUnequal( var CodeTree: pCodeTree); virtual;
    procedure DoGreater( var CodeTree: pCodeTree); virtual;
    procedure DoLess( var CodeTree: pCodeTree); virtual;
    procedure DoGreaterEqual( var CodeTree: pCodeTree); virtual;
    procedure DoLessEqual( var CodeTree: pCodeTree); virtual;}
    procedure DoIN( var CodeTree: pCodeTree); virtual;
    procedure DoPred( CodeTree: pCodeTree); virtual;
    procedure DoSucc( CodeTree: pCodeTree); virtual;
    procedure DoInc( CodeTree: pCodeTree); virtual;
    procedure DoDec( CodeTree: pCodeTree); virtual;
    procedure DoLength( CodeTree: pCodeTree); virtual;
    procedure DoAssign( CodeTree: pCodeTree); virtual;
    procedure DoWrite( CodeTree: pCodeTree); virtual;
    procedure DoRead( CodeTree: pCodeTree); virtual;
    procedure DoArithmeticFunction( CodeTree: pCodeTree); virtual;
    procedure DoNewDispose( CodeTree: pCodeTree); virtual;
    procedure DoAssigned( CodeTree: pCodeTree); virtual;
    procedure DoConcat( CodeTree: pCodeTree); virtual;
    procedure DoIncludeExclude( CodeTree: pCodeTree; FuncName: String); virtual;
    procedure DoFunction( CodeTree: pCodeTree); virtual;
    procedure DoMem( CodeTree: pCodeTree); virtual;
    procedure DoPort( CodeTree: pCodeTree); virtual;
    procedure DoTypeOfExpression( CodeTree: pCodeTree); virtual;
    procedure DoTypeOfType( CodeTree: pCodeTree); virtual;
    procedure PushSet( CodeTree: pCodeTree);
    procedure DoCompare( var CodeTree: pCodeTree; CodeType: tCodeType);
    procedure DoIfExpression( CodeTree: pCodeTree);

    procedure CopyMemory( Count: LongInt); virtual;
    procedure CopyObject( VMT: String); virtual;

    procedure GetReference( CodeTree: pCodeTree; Register: tRegister;
      var Ref: tReference); virtual;

    procedure DoAsmBlock( CodeTree: pCodeTree);
    procedure DoIFBlock( CodeTree: pCodeTree);
    procedure DoWhileBlock( CodeTree: pCodeTree);
    procedure DoRepeatUntilBlock( CodeTree: pCodeTree);
    procedure DoFORBlock( CodeTree: pCodeTree);
    procedure DoCASEBlock( CodeTree: pCodeTree);
    procedure DoWITHblock( CodeTree: pCodeTree);
    procedure DoBreak;
    procedure DoContinue;
    procedure DoEXIT;
    procedure DoRealConst( CodeTree: pCodeTree);
    procedure DoLoadIntConstToFpuStack( CodeTree: pCodeTree);
    procedure DoLabel( CodeTree: pCodeTree);
    procedure DoGOTO( CodeTree: pCodeTree);

    function GetRegister( LockedReg: tRegister): tRegister;
    procedure UseRegister( Reg: tRegister; var IsPush: Boolean);
    procedure ReleaseRegister( Reg: tRegister; IsPush: Boolean);
    procedure LockRegister( Reg: tRegister);
    procedure UnlockRegister( Reg: tRegister);

    procedure PushUsedRegisters;
    procedure PopUsedRegisters;
    procedure PushLoop( const EndLab, ConditionLab: String);
    procedure PopLoop;

    procedure IncTempSize( L: LongInt);
    procedure DecTempSize( L: LongInt);
  end;

implementation

uses StdLib, Tools, Errors, BasmComp, Compiler;

{ tCodeGenarator }
constructor tCodeGenerator.Init( aLexLevel: Byte; aLocalSize: LongInt);
  begin
    inherited Init;
    LexLevel := aLexLevel;
    Res := New( pProcAsm, Init);
    UsedRegisters := [];
    LocalSize := aLocalSize;
    ExitLabel := NewStr( CurCompiler^.CreateLabel);
  end;

destructor tCodeGenerator.Done;
  begin
    if Assigned( ExitLabel) then
      begin
        Res^.Concat( MakeLabel( New( pAsmInstruction, Create(
          caiNoInstruction)), ExitLabel^));
        DisposeStr( ExitLabel);
      end;
    inherited Done;
  end;

procedure tCodeGenerator.DoBlock( CodeTree: pCodeTree);
  var
    Code: pCodeTree;
  begin
    if Assigned( CodeTree) then
      begin
        Code := CodeTree^.Right;
        while Assigned( Code) do
          begin
            GenerateAsm( Code);
            Code := Code^.Left;
          end;
      end;
  end;

procedure tCodeGenerator.DoExpression( CodeTree: pCodeTree);
  begin
    if Assigned( CodeTree) then
      begin
        case CodeTree^.Node.CodeType of
          cctAddition:
            DoAddition( CodeTree);
          cctSubtraction:
            DoSubtraction( CodeTree);
          cctMultiplication:
            DoMultiplication( CodeTree);
          cctDiv:
            DoDiv( CodeTree);
          cctMod:
            DoMod( CodeTree);
          cctDivision:
            DoDivision( CodeTree);
          cctVariable:
            DoVariable( CodeTree);
          cctAssignment:
            DoAssignment( CodeTree);
          cctLoadValue,
          cctWithSymbol:
            DoLoadValue( CodeTree);
          cctIntConst,
          cctOrdConst,
          cctCharConst,
          cctPointerConst:
            if CodeTree^.Location.Location = clRegister then
              begin
                if CodeTree^.Node.PointerSymbol = nil then
                  Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                    caiMov, CodeTree^.Location.Register,
                    CodeTree^.Node.PointerValue)))
                else
                  Res^.Concat( New( pAsmInstruction, Create_Reg_Offset(
                    caiMov, CodeTree^.Location.Register,
                    CodeTree^.Node.PointerSymbol^.AsmName,
                    CodeTree^.Node.PointerValue)))
              end;
          cctBoolConst:
            if CodeTree^.Location.Location = clFlags then
              begin
                if Assigned( CodeTree^.Location.LabelTrue) then
                  begin
                    if CodeTree^.Node.BoolValue then
                      Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                        caiJMP, CodeTree^.Location.LabelTrue^)))
                    else
                      Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                        caiJMP, CodeTree^.Location.LabelFalse^)));
                  end
                else
                  begin
                    if CodeTree^.Node.BoolValue then
                      Res^.Concat( New( pAsmInstruction, Create(
                        caiCLC)))
                    else
                      Res^.Concat( New( pAsmInstruction, Create(
                        caiSTC)));
                    CodeTree^.Location.ResultFlag := cfNoCarry;
                  end;
              end;
          cctStringConst:
            DoStringConst( CodeTree);
          cctPCharConst:
            DoPCharConst( CodeTree);
          cctRealConst:
            DoRealConst( CodeTree);
          cctTypeConversion:
            DoTypeConversion( CodeTree);
          cctDeref:
            DoDeref( CodeTree);
          cctFunctionCall:
            DoFunctionCall( CodeTree);
          cctLoadAddress:
            DoLoadAddress( CodeTree);
          cctAnd:
            DoAnd( CodeTree);
          cctOr:
            DoOr( CodeTree);
          cctXor:
            DoXor( CodeTree);
          cctNot:
            DoNot( CodeTree);
          cctNeg:
            DoNeg( CodeTree);
          cctShr:
            DoShrShl( CodeTree, caiSHR);
          cctShl:
            DoShrShl( CodeTree, caiSHL);

          cctEqual,
          cctUnequal,
          cctGreater,
          cctLess,
          cctGreaterEq,
          cctLessEq:
            DoCompare( CodeTree, CodeTree^.Node.CodeType);

          cctIN:
            DoIN( CodeTree);
          cctPred:
            DoPred( CodeTree);
          cctSucc:
            DoSucc( CodeTree);
          cctInc:
            DoInc( CodeTree);
          cctDec:
            DoDec( CodeTree);
          cctSetConst:
            DoSetConst( CodeTree);
          cctSetItem:
            DoSetItem( CodeTree);
          cctSetRange:
            DoSetRange( CodeTree);
          cctLength:
            DoLength( CodeTree);
          cctAssign:
            DoAssign( CodeTree);
          cctWrite,
          cctWriteLn:
            DoWrite( CodeTree);
          cctRead,
          cctReadLn:
            DoRead( CodeTree);
          cctArithmeticFunction:
            DoArithmeticFunction( CodeTree);
          cctNew,
          cctDispose:
            DoNewDispose( CodeTree);
          cctAssigned:
            DoAssigned( CodeTree);
          cctFunction:
            DoFunction( CodeTree);
          cctConcat:
            DoConcat( CodeTree);
          cctInclude:
            DoIncludeExclude( CodeTree, NameSetInclude);
          cctExclude:
            DoIncludeExclude( CodeTree, NameSetExclude);
          cctMem:
            DoMem( CodeTree);
          cctPort:
            DoPort( CodeTree);
          cctTypeOfExpression:
            DoTypeOfExpression( CodeTree);
          cctTypeOfType:
            DoTypeOfType( CodeTree);
          cctIfBlock:
            DoIfExpression( CodeTree);
        end;
      end;
  end;

procedure tCodeGenerator.DoAddition( CodeTree: pCodeTree);
  var
    Ref: tReference;
    ResReg: tRegister;
    IsPush: Boolean;
    AI: pAsmInstruction;
    OldUsedRegisters: tRegisterSet;
    OldCounter: LongInt;
  begin
    case CodeTree^.ResType^.DefType of
      cUserOrdDefinition,
      cOrdDefinition:
        begin
          CodeTree^.Left^.Location := CodeTree^.Location;
          DoExpression( CodeTree^.Left);
          if CodeTree^.Location.Location = clRegister then
            begin
              case CodeTree^.Right^.Node.CodeType of
                cctIntConst:
                  if CodeTree^.Right^.Node.IntValue <> 1 then
                    Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                      caiADD, CodeTree^.Location.Register, CodeTree^.Right^.Node.IntValue)))
                  else
                    Res^.Concat( New( pAsmInstruction, Create_Reg(
                      caiINC, CodeTree^.Location.Register )));
                else
                  begin
                    LockRegister( CodeTree^.Location.Register);
                    ResReg := GetRegister( CodeTree^.Location.Register);
                    UseRegister( ResReg, IsPush);
                    CodeTree^.Right^.Location.Location := clRegister;
                    CodeTree^.Right^.Location .Register:= ResReg;
                    DoExpression( CodeTree^.Right);
                    Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                      caiADD, CodeTree^.Location.Register, ResReg )));
                    ReleaseRegister( ResReg, IsPush);
                    UnlockRegister( CodeTree^.Location.Register);
                  end;
              end;
          end;
        end;

      cRealDefinition:
        if (CodeTree^.Left^.ResType^.DefType = cRealDefinition) and
          (CodeTree^.Right^.ResType^.DefType = cRealDefinition) then
        begin
          CodeTree^.Left^.Location.Location := clFPUStack;
          CodeTree^.Left^.Location.Register := crST;
          DoExpression( CodeTree^.Left);
          CodeTree^.Right^.Location.Location := clFPUStack;
          CodeTree^.Right^.Location.Register := crST;
          DoExpression( CodeTree^.Right);
          Res^.Concat( New( pAsmInstruction, Create(
            caiFADD)));
          case CodeTree^.Location.Location of
            clFPUStack:
              if not (CodeTree^.Location.Register in [crST, crST0]) then
                Res^.Concat( New( pAsmInstruction, Create_Reg(
                  caiFSTP, CodeTree^.Location.Register)));
          end;
        end;

      cStringDefinition: if CodeTree^.Location.Location = clMemory then
        begin
          OldCounter := Counter;
          Counter := 0;
          CodeTree^.Left^.Location := CodeTree^.Location;
          DoExpression( CodeTree^.Left);

          PushUsedRegisters;
          OldUsedRegisters := UsedRegisters;
          UsedRegisters := [];
          Res^.Concat(
            _LEA_( crEAX, CodeTree^.Location.Reference));
          Res^.Concat(
            _PUSH_( crEAX));
          IsPush := False;
          if not (CodeTree^.Right^.Node.CodeType in [ cctStringConst,
            cctVariable, cctWithSymbol, cctLoadValue, cctDeref]) then
            begin
              IncTempSize( 256);
              IsPush := True;
              CodeTree^.Right^.Location.Location := clMemory;
              CreateReference( crDefaultSeg, crEBP, crNoRegister,
                1, -CurTempSize-LocalSize, nil, csDefault,
                CodeTree^.Right^.Location.Reference);
              DoExpression( CodeTree^.Right);
              Res^.Concat(
                _LEA_( crEAX, CodeTree^.Right^.Location.Reference));
              Res^.Concat(
                _PUSH_( crEAX));
              {DecTempSize( 256);}
            end
          else
            begin
              CodeTree^.Right^.Location.Location := clRegister;
              CodeTree^.Right^.Location.Register := crEAX;
              UseRegister( crEAX, IsPush);
              DoExpression( CodeTree^.Right);
              Res^.Concat(
                _PUSH_( crEAX));
              ReleaseRegister( crEAX, IsPush);
              IsPush := False;
            end;
          Res^.Concat(
            _PUSH_const( CodeTree^.ResType^.GetSize - 1));
          Res^.Concat( New( pAsmInstruction, Create_JSymbol(
            caiCALL, NameStrCat)));
          UsedRegisters := OldUsedRegisters;
          PopUsedRegisters;
          if Counter <> 0 then
            DecTempSize( Counter);
          Counter := OldCounter;
        end;

      cPointerDefinition: if CodeTree^.Location.Location = clRegister then
        begin
          CodeTree^.Left^.Location := CodeTree^.Location;
          DoExpression( CodeTree^.Left);

          LockRegister( CodeTree^.Location.Register);
          ResReg := GetRegister( CodeTree^.Location.Register);
          UseRegister( ResReg, IsPush);
          CodeTree^.Right^.Location.Location := clRegister;
          CodeTree^.Right^.Location .Register:= ResReg;
          DoExpression( CodeTree^.Right);
          if pPointerDefinition( CodeTree^.Left^.ResType)^.DefinitionType^.GetSize <> 1 then
            Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
              caiIMUL, ResReg,
              pPointerDefinition( CodeTree^.Left^.ResType)^.DefinitionType^.GetSize )));
          Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
            caiADD, CodeTree^.Location.Register, ResReg )));
          ReleaseRegister( ResReg, IsPush);
          UnlockRegister( CodeTree^.Location.Register);
        end;

      cSetDefinition: if CodeTree^.Location.Location = clMemory then
        begin
          OldUsedRegisters := UsedRegisters;
          OldCounter := Counter;
          Counter := 0;
          PushUsedRegisters;
          UsedRegisters := [];

          CodeTree^.Left^.Location := CodeTree^.Location;
          DoExpression( CodeTree^.Left);
          Res^.Concat(
            _LEA_( crEAX, CodeTree^.Location.Reference));
          Res^.Concat(
            _PUSH_( crEAX));

          case CodeTree^.Right^.Node.CodeType of
            cctSetItem:
              begin
                CodeTree^.Right^.Left^.Location.Location := clRegister;
                CodeTree^.Right^.Left^.Location.Register := crEAX;
                DoExpression( CodeTree^.Right^.Left);
                Res^.Concat(
                  _PUSH_( crEAX));
                Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                  caiCALL, NameSetSetItem)));
              end;
            cctSetRange:
              begin
                CodeTree^.Right^.Left^.Location.Location := clRegister;
                CodeTree^.Right^.Left^.Location.Register := crEAX;
                DoExpression( CodeTree^.Right^.Left);
                Res^.Concat(
                  _PUSH_( crEAX));

                CodeTree^.Right^.Right^.Location.Location := clRegister;
                CodeTree^.Right^.Right^.Location.Register := crEAX;
                DoExpression( CodeTree^.Right^.Right);
                Res^.Concat(
                  _PUSH_( crEAX));

                Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                  caiCALL, NameSetSetRange)));
              end;
            else
              begin
                IncTempSize( 32);

                CodeTree^.Right^.Location.Location := clMemory;
                CreateReference( crDefaultSeg, crEBP, crNoRegister,
                  1, -CurTempSize-LocalSize, nil, csDefault,
                  CodeTree^.Right^.Location.Reference);
                DoExpression( CodeTree^.Right);
                Res^.Concat(
                  _LEA_( crEAX, CodeTree^.Right^.Location.Reference));
                Res^.Concat(
                  _PUSH_( crEAX));

                Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                  caiCALL, NameSetUnion)));

                {DecTempSize( 32);}
              end;
          end;

          UsedRegisters := OldUsedRegisters;
          PopUsedRegisters;
          if Counter <> 0 then
            DecTempSize( Counter);
          Counter := OldCounter;
        end;
    end;
  end;

procedure tCodeGenerator.DoSubtraction( CodeTree: pCodeTree);
  var
    Sym: pVariableSymbol;
    Ref: tReference;
    ResReg: tRegister;
    IsPush: Boolean;
    OldUsedRegisters: tRegisterSet;
    OldCounter: LongInt;
  begin
    case CodeTree^.ResType^.DefType of
      cUserOrdDefinition,
      cOrdDefinition:
        begin
          CodeTree^.Left^.Location := CodeTree^.Location;
          DoExpression( CodeTree^.Left);
          if CodeTree^.Location.Location = clRegister then
            begin
              case CodeTree^.Right^.Node.CodeType of
                cctIntConst:
                  if CodeTree^.Right^.Node.IntValue <> 1 then
                    Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                      caiSUB, CodeTree^.Location.Register, CodeTree^.Right^.Node.IntValue)))
                  else
                    Res^.Concat( New( pAsmInstruction, Create_Reg(
                      caiDEC, CodeTree^.Location.Register )));
                else
                  begin
                    LockRegister( CodeTree^.Location.Register);
                    ResReg := GetRegister( CodeTree^.Location.Register);
                    UseRegister( ResReg, IsPush);
                    CodeTree^.Right^.Location.Location := clRegister;
                    CodeTree^.Right^.Location .Register:= ResReg;
                    DoExpression( CodeTree^.Right);
                    Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                      caiSUB, CodeTree^.Location.Register, ResReg )));
                    ReleaseRegister( ResReg, IsPush);
                    UnlockRegister( CodeTree^.Location.Register);
                  end;
              end;
          end;
        end;

      cRealDefinition:
        if (CodeTree^.Left^.ResType^.DefType = cRealDefinition) and
          (CodeTree^.Right^.ResType^.DefType = cRealDefinition) then
        begin
          CodeTree^.Left^.Location.Location := clFPUStack;
          CodeTree^.Left^.Location.Register := crST;
          DoExpression( CodeTree^.Left);
          CodeTree^.Right^.Location.Location := clFPUStack;
          CodeTree^.Right^.Location.Register := crST;
          DoExpression( CodeTree^.Right);
          Res^.Concat( New( pAsmInstruction, Create(
            caiFSUB)));
          case CodeTree^.Location.Location of
            clFPUStack:
              if not (CodeTree^.Location.Register in [crST, crST0]) then
                Res^.Concat( New( pAsmInstruction, Create_Reg(
                  caiFSTP, CodeTree^.Location.Register)));
          end;
        end;

      cPointerDefinition: if CodeTree^.Location.Location = clRegister then
        begin
          CodeTree^.Left^.Location := CodeTree^.Location;
          DoExpression( CodeTree^.Left);

          LockRegister( CodeTree^.Location.Register);
          ResReg := GetRegister( CodeTree^.Location.Register);
          UseRegister( ResReg, IsPush);
          CodeTree^.Right^.Location.Location := clRegister;
          CodeTree^.Right^.Location .Register:= ResReg;
          DoExpression( CodeTree^.Right);
          if pPointerDefinition( CodeTree^.Left^.ResType)^.DefinitionType^.GetSize <> 1 then
            Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
              caiIMUL, ResReg,
              pPointerDefinition( CodeTree^.Left^.ResType)^.DefinitionType^.GetSize )));
          Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
            caiSUB, CodeTree^.Location.Register, ResReg )));
          ReleaseRegister( ResReg, IsPush);
          UnlockRegister( CodeTree^.Location.Register);
        end;

      cSetDefinition: if CodeTree^.Location.Location = clMemory then
        begin
          OldCounter := Counter;
          Counter := 0;
          OldUsedRegisters := UsedRegisters;
          PushUsedRegisters;
          UsedRegisters := [];

          CodeTree^.Left^.Location := CodeTree^.Location;
          DoExpression( CodeTree^.Left);
          Res^.Concat(
            _LEA_( crEAX, CodeTree^.Location.Reference));
          Res^.Concat(
            _PUSH_( crEAX));

          IncTempSize( 32);

          CodeTree^.Right^.Location.Location := clMemory;
          CreateReference( crDefaultSeg, crEBP, crNoRegister,
            1, -CurTempSize-LocalSize, nil, csDefault,
            CodeTree^.Right^.Location.Reference);
          DoExpression( CodeTree^.Right);
          Res^.Concat(
            _LEA_( crEAX, CodeTree^.Right^.Location.Reference));
          Res^.Concat(
            _PUSH_( crEAX));

          Res^.Concat( New( pAsmInstruction, Create_JSymbol(
            caiCALL, NameSetDifference)));

          {DecTempSize( 32);}

          UsedRegisters := OldUsedRegisters;
          PopUsedRegisters;
          if Counter <> 0 then
            DecTempSize( Counter);
          Counter := OldCounter;
        end;
    end;
  end;

procedure tCodeGenerator.DoMultiplication( CodeTree: pCodeTree);
  var
    Sym: pVariableSymbol;
    Ref: tReference;
    ResReg: tRegister;
    IsPush: Boolean;
    OldUsedRegisters: tRegisterSet;
    OldCounter: LongInt;
  begin
    case CodeTree^.ResType^.DefType of
      cUserOrdDefinition,
      cOrdDefinition:
        begin
          CodeTree^.Left^.Location := CodeTree^.Location;
          DoExpression( CodeTree^.Left);
          if CodeTree^.Location.Location = clRegister then
            begin
              case CodeTree^.Right^.Node.CodeType of
                cctIntConst:
                  if CodeTree^.Right^.Node.IntValue <> 1 then
                    Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                      caiIMUL, CodeTree^.Location.Register, CodeTree^.Right^.Node.IntValue)));
                else
                  begin
                    LockRegister( CodeTree^.Location.Register);
                    ResReg := GetRegister( CodeTree^.Location.Register);
                    UseRegister( ResReg, IsPush);
                    CodeTree^.Right^.Location.Location := clRegister;
                    CodeTree^.Right^.Location.Register:= ResReg;
                    DoExpression( CodeTree^.Right);
                    Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                      caiIMUL, CodeTree^.Location.Register, ResReg )));
                    ReleaseRegister( ResReg, IsPush);
                    UnlockRegister( CodeTree^.Location.Register);
                  end;
              end;
          end;
        end;

      cRealDefinition:
        if (CodeTree^.Left^.ResType^.DefType = cRealDefinition) and
          (CodeTree^.Right^.ResType^.DefType = cRealDefinition) then
        begin
          CodeTree^.Left^.Location.Location := clFPUStack;
          CodeTree^.Left^.Location.Register := crST;
          DoExpression( CodeTree^.Left);
          CodeTree^.Right^.Location.Location := clFPUStack;
          CodeTree^.Right^.Location.Register := crST;
          DoExpression( CodeTree^.Right);
          Res^.Concat( New( pAsmInstruction, Create(
            caiFMUL)));
          case CodeTree^.Location.Location of
            clFPUStack:
              if not (CodeTree^.Location.Register in [crST, crST0]) then
                Res^.Concat( New( pAsmInstruction, Create_Reg(
                  caiFSTP, CodeTree^.Location.Register)));
          end;
        end;

      cSetDefinition: if CodeTree^.Location.Location = clMemory then
        begin
          OldCounter := Counter;
          Counter := 0;
          OldUsedRegisters := UsedRegisters;
          PushUsedRegisters;
          UsedRegisters := [];

          CodeTree^.Left^.Location := CodeTree^.Location;
          DoExpression( CodeTree^.Left);
          Res^.Concat(
            _LEA_( crEAX, CodeTree^.Location.Reference));
          Res^.Concat(
            _PUSH_( crEAX));

          IncTempSize( 32);

          CodeTree^.Right^.Location.Location := clMemory;
          CreateReference( crDefaultSeg, crEBP, crNoRegister,
            1, -CurTempSize-LocalSize, nil, csDefault,
            CodeTree^.Right^.Location.Reference);
          DoExpression( CodeTree^.Right);
          Res^.Concat(
            _LEA_( crEAX, CodeTree^.Right^.Location.Reference));
          Res^.Concat(
            _PUSH_( crEAX));

          Res^.Concat( New( pAsmInstruction, Create_JSymbol(
            caiCALL, NameSetIntersect)));

          {DecTempSize( 32);}

          UsedRegisters := OldUsedRegisters;
          PopUsedRegisters;
          if Counter <> 0 then
            DecTempSize( Counter);
          Counter := OldCounter;
        end;
    end;
  end;

procedure tCodeGenerator.DoDiv( CodeTree: pCodeTree);
  var
    Ref: pReference;
    IsEAXPush, IsEDXPush, IsEBXPush: Boolean;
    Reg: tRegister;
  begin
    if CodeTree^.Location.Location = clRegister then
      begin
        IsEAXPush := False;
        IsEDXPush := False;
        IsEBXPush := False;
        Reg := CodeTree^.Location.Register;
        if Reg <> crEAX then
          UseRegister( crEAX, IsEAXPush);
        CodeTree^.Left^.Location.Location := clRegister;
        CodeTree^.Left^.Location.Register := crEAX;
        DoExpression( CodeTree^.Left);

        LockRegister( crEAX);
        if Reg <> crEBX then
          UseRegister( crEBX, IsEBXPush);
        CodeTree^.Right^.Location.Location := clRegister;
        CodeTree^.Right^.Location.Register := crEBX;
        DoExpression( CodeTree^.Right);
        UnlockRegister( crEAX);

        if Reg <> crEDX then
          UseRegister( crEDX, IsEDXPush);
        Res^.Concat( New( pAsmInstruction, Create( caiCDQ)));
        Res^.Concat( New( pAsmInstruction, Create_Reg(
          caiIDIV, crEBX)));
        if CodeTree^.Location.Register <> crEAX then
          Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
            caiMOV, Reg, crEAX)));
        if Reg <> crEDX then
          ReleaseRegister( crEDX, IsEDXPush);
        if Reg <> crEBX then
          ReleaseRegister( crEBX, IsEBXPush);
        if Reg <> crEAX then
          ReleaseRegister( crEAX, IsEAXPush);
      end;
  end;

procedure tCodeGenerator.DoMod( CodeTree: pCodeTree);
  var
    Ref: pReference;
    IsEAXPush, IsEDXPush, IsEBXPush: Boolean;
    Reg: tRegister;
  begin
    if CodeTree^.Location.Location = clRegister then
      begin
        IsEAXPush := False;
        IsEDXPush := False;
        IsEBXPush := False;
        Reg := CodeTree^.Location.Register;
        if Reg <> crEAX then
          UseRegister( crEAX, IsEAXPush);
        CodeTree^.Left^.Location.Location := clRegister;
        CodeTree^.Left^.Location.Register := crEAX;
        DoExpression( CodeTree^.Left);

        LockRegister( crEAX);
        if Reg <> crEBX then
          UseRegister( crEBX, IsEBXPush);
        CodeTree^.Right^.Location.Location := clRegister;
        CodeTree^.Right^.Location.Register := crEBX;
        DoExpression( CodeTree^.Right);
        UnlockRegister( crEAX);

        if Reg <> crEDX then
          UseRegister( crEDX, IsEDXPush);
        Res^.Concat( New( pAsmInstruction, Create( caiCDQ)));
        Res^.Concat( New( pAsmInstruction, Create_Reg(
          caiIDIV, crEBX)));
        if CodeTree^.Location.Register <> crEDX then
          Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
            caiMOV, Reg, crEDX)));
        if Reg <> crEDX then
          ReleaseRegister( crEDX, IsEDXPush);
        if Reg <> crEBX then
          ReleaseRegister( crEBX, IsEBXPush);
        if Reg <> crEAX then
          ReleaseRegister( crEAX, IsEAXPush);
      end;
  end;

procedure tCodeGenerator.DoDivision( CodeTree: pCodeTree);
  begin
    if CodeTree^.ResType^.DefType = cRealDefinition then
      begin
        if (CodeTree^.Left^.ResType^.DefType = cRealDefinition) and
          (CodeTree^.Right^.ResType^.DefType = cRealDefinition) then
          begin
            CodeTree^.Left^.Location.Location := clFPUStack;
            CodeTree^.Left^.Location.Register := crST;
            DoExpression( CodeTree^.Left);
            CodeTree^.Right^.Location.Location := clFPUStack;
            CodeTree^.Right^.Location.Register := crST;
            DoExpression( CodeTree^.Right);
            Res^.Concat( New( pAsmInstruction, Create(
              caiFDIV)));
            case CodeTree^.Location.Location of
              clFPUStack:
                if not (CodeTree^.Location.Register in [crST, crST0]) then
                  Res^.Concat( New( pAsmInstruction, Create_Reg(
                    caiFSTP, CodeTree^.Location.Register)));
            end;
          end;
      end;
  end;

procedure tCodeGenerator.DoAssignment( CodeTree: pCodeTree);
  var
    Ref, R: tReference;
    VarSym: pVariableSymbol;
    ResReg, Reg: tRegister;
    IsPush, B: Boolean;
    AsmCom: tAsmOp;
    AI: pAsmInstruction;
    Lab, LabTrue, LabFalse: String;
    OldUsedRegisters: tRegisterSet;
    Size: tSize;
    OldCounter: LongInt;
  begin
    VarSym := CodeTree^.Left^.Node.Symbol;
    case CodeTree^.ResType^.DefType of
      cRealDefinition:
        begin
          CodeTree^.Right^.Location.Location := clFPUStack;
          CodeTree^.Right^.Location.Register := crST;
          DoExpression( CodeTree^.Right);
          ResReg := GetRegister( crNoRegister);
          UseRegister( ResReg, IsPush);
          GetReference( CodeTree^.Left, ResReg, Ref);
          if CodeTree^.Location.Location = clNone then
            Res^.Concat( New( pAsmInstruction, Create_Ref(
              caiFSTP, Ref)))
          else if  CodeTree^.Location.Location = clFPUStack then
            begin
              Res^.Concat( New( pAsmInstruction, Create_Reg(
                caiFLD, crST0)));
              Res^.Concat( New( pAsmInstruction, Create_Ref(
                caiFSTP, Ref)));
              if not (CodeTree^.Location.Register in [crST0, crST]) then
                Res^.Concat( New( pAsmInstruction, Create_Reg(
                  caiFSTP, CodeTree^.Location.Register)));
            end;
          ReleaseRegister( ResReg, IsPush);
        end;

      cBooleanDefinition:
        begin
          LabTrue := CurCompiler^.CreateLabel;
          LabFalse := CurCompiler^.CreateLabel;
          Lab := CurCompiler^.CreateLabel;

          ResReg := GetRegister( crNoRegister);
          UseRegister( ResReg, IsPush);
          GetReference( CodeTree^.Left, ResReg, Ref);
          LockRegister( ResReg);

          if (CodeTree^.Location.Location = clNone) and
            (CodeTree^.Right^.Node.CodeType = cctBoolConst) then
            begin
              Res^.Concat( New( pAsmInstruction, Create_Ref_Const(
                caiMOV, Ref, CodeTree^.Right^.Node.IntValue)));
            end
          else
            begin
              CodeTree^.Right^.Location.Location := clFlags;
              CodeTree^.Right^.Location.LabelTrue := NewStr( LabTrue);
              CodeTree^.Right^.Location.LabelFalse := NewStr( LabFalse);
              DoExpression( CodeTree^.Right);

              Res^.Concat( MakeLabel( New( pAsmInstruction, Create( caiNoInstruction)),
                LabTrue));
              Res^.Concat( New( pAsmInstruction, Create_Ref_Const(
                caiMOV, Ref, 1)));
              Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                caiJMP, Lab)));

              Res^.Concat( MakeLabel( New( pAsmInstruction, Create( caiNoInstruction)),
                LabFalse));
              Res^.Concat( New( pAsmInstruction, Create_Ref_Const(
                caiMOV, Ref, 0)));

              Res^.Concat( MakeLabel( New( pAsmInstruction, Create( caiNoInstruction)),
                Lab));
              if CodeTree^.Location.Location = clFlags then
                Res^.Concat( New( pAsmInstruction, Create_Ref_Const(
                  caiCMP, Ref, 0)));
              ReleaseRegister( ResReg, IsPush);
              CodeTree^.Location.ResultFlag := cfNotEqual;
              if (CodeTree^.Location.Location = clFlags) and
                Assigned( CodeTree^.Location.LabelTrue) then
                begin
                  Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                    caiJNZ, CodeTree^.Location.LabelTrue^)));
                  Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                    caiJMP, CodeTree^.Location.LabelFalse^)));
                end;
            end;
          UnlockRegister( ResReg);
        end;

      cOrdDefinition,
      cUserOrdDefinition,
      cPointerDefinition,
      cFunctionTypeDefinition:
        case CodeTree^.Left^.Node.CodeType of
          cctMem:
            begin
              if CodeTree^.Location.Location = clRegister then
                ResReg := CodeTree^.Location.Register
              else
                begin
                  ResReg := GetRegister( crNoRegister);
                  UseRegister( ResReg, IsPush);
                end;
              CodeTree^.Left^.Left^.Location.Location := clRegister;
              CodeTree^.Left^.Left^.Location.Register := ResReg;
              DoExpression( CodeTree^.Left^.Left);

              LockRegister( ResReg);
              Reg := GetRegister( ResReg);
              UseRegister( Reg, B);
              CodeTree^.Right^.Location.Location := clRegister;
              CodeTree^.Right^.Location.Register := Reg;
              DoExpression( CodeTree^.Right);
              Size := GetSize( CodeTree^.ResType^.GetSize);
              CreateReference( crFS, ResReg, crNoRegister, 1, 0, nil, Size, Ref);
              Res^.Concat( New( pAsmInstruction, Create_Ref_Reg(
                caiMOV, Ref, GetReg( Reg, Size) )));
              if CodeTree^.Location.Location <> clRegister then
                begin
                  ReleaseRegister( Reg, B);
                  UnlockRegister( ResReg);
                  ReleaseRegister( ResReg, IsPush);
                end
              else
                begin
                  Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                    caiMOV, ResReg, Reg)));
                  ReleaseRegister( Reg, B);
                  UnlockRegister( ResReg);
                end;
            end;
          cctPort:
            begin
              if CodeTree^.Location.Location = clRegister then
                ResReg := CodeTree^.Location.Register
              else
                ResReg := crNoRegister;
              if ResReg <> crEDX then
                UseRegister( crEDX, IsPush);
              CodeTree^.Left^.Left^.Location.Location := clRegister;
              CodeTree^.Left^.Left^.Location.Register := crEDX;
              DoExpression( CodeTree^.Left^.Left);

              LockRegister( crEDX);
              Reg := GetRegister( ResReg);
              if ResReg <> crEAX then
                UseRegister( crEAX, B);
              CodeTree^.Right^.Location.Location := clRegister;
              CodeTree^.Right^.Location.Register := Reg;
              DoExpression( CodeTree^.Right);
              Size := GetSize( CodeTree^.ResType^.GetSize);
              Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                caiOUT, crDX, GetReg( crEAX, Size) )));
              UnlockRegister( crEDX);
              if CodeTree^.Location.Location <> clRegister then
                begin
                  ReleaseRegister( crEAX, B);
                  ReleaseRegister( crEDX, IsPush);
                end
              else
                begin
                  Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                    caiMOV, ResReg, crEAX)));
                  if ResReg <> crEAX then
                    ReleaseRegister( crEAX, B);
                  if ResReg <> crEDX then
                    ReleaseRegister( crEDX, IsPush);
                end;
            end;
          else
              if CodeTree^.Location.Location = clNone then
                begin
                  ResReg := GetRegister( crNoRegister);
                  UseRegister( ResReg, IsPush);
                  CodeTree^.Right^.Location.Location := clRegister;
                  CodeTree^.Right^.Location.Register := ResReg;
                  DoExpression( CodeTree^.Right);

                  LockRegister( ResReg);
                  Reg := GetRegister( ResReg);
                  UseRegister( Reg, B);
                  GetReference( CodeTree^.Left, Reg, Ref);
                  Res^.Concat( New( pAsmInstruction, Create_Ref_Reg(
                    caiMov, Ref, GetReg( ResReg, Ref.Size))));
                  ReleaseRegister( Reg, B);
                  UnlockRegister( ResReg);
                  ReleaseRegister( ResReg, IsPush);
                end
              else if CodeTree^.Location.Location = clRegister then
                    begin
                      CodeTree^.Right^.Location := CodeTree^.Location;
                      DoExpression( CodeTree^.Right);
                      ResReg := CodeTree^.Location.Register;

                      LockRegister( ResReg);
                      Reg := GetRegister( ResReg);
                      UseRegister( Reg, IsPush);
                      GetReference( CodeTree^.Left, Reg, Ref);
                      Res^.Concat( New( pAsmInstruction, Create_Ref_Reg(
                        caiMov, Ref, GetReg( ResReg, Ref.Size))));
                      ReleaseRegister( Reg, IsPush);
                      UnlockRegister( ResReg);
                    end;
        end;

      cStringDefinition:
        begin
          PushUsedRegisters;
          OldUsedRegisters := UsedRegisters;
          OldCounter := Counter;
          Counter := 0;
          UsedRegisters := [];
          ResReg := crNoRegister;

          case CodeTree^.Location.Location of
            clRegister,
            clNone:
              begin
                IncTempSize( CodeTree^.ResType^.GetSize);
                CodeTree^.Right^.Location.Location := clMemory;
                CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
                  -CurTempSize-LocalSize, nil, csDefault,
                  CodeTree^.Right^.Location.Reference);
              end;
            clMemory:
              begin
                CodeTree^.Right^.Location := CodeTree^.Location;
                ResReg := CodeTree^.Location.Reference.Base;
                if (ResReg in [crEAX, crEBX, crECX, crEDX]) then
                  UseRegister( ResReg, IsPush);
              end;
          end;

          LockRegister( ResReg);
          Reg := GetRegister( ResReg);
          UseRegister( Reg, B);
          GetReference( CodeTree^.Left, Reg, Ref);
          ReleaseRegister( Reg, B);
          Res^.Concat(
            _PUSH_( Reg));
          UnlockRegister( ResReg);

          DoExpression( CodeTree^.Right);
          Res^.Concat(
            _LEA_( crEAX, CodeTree^.Right^.Location.Reference));
          Res^.Concat(
            _PUSH_( crEAX));

          Res^.Concat(
            _PUSH_const( pStringDefinition( CodeTree^.ResType)^.Length));

          Res^.Concat( New( pAsmInstruction, Create_JSymbol(
            caiCALL, NameStrCopy)));

          UsedRegisters := OldUsedRegisters;
          PopUsedRegisters;
          if Counter <> 0 then
            DecTempSize( Counter);
          Counter := OldCounter;
          if CodeTree^.Location.Location in [ clRegister, clNone] then
            begin
              {DecTempSize( CodeTree^.ResType^.GetSize);}
              if CodeTree^.Location.Location = clRegister then
                Res^.Concat(
                  _LEA_( CodeTree^.Location.Register,
                    CodeTree^.Right^.Location.Reference));
            end;
        end;

      cObjectDefinition:
        begin
          case CodeTree^.Location.Location of
            clRegister:
              ResReg := CodeTree^.Location.Register;
            clNone:
              begin
                ResReg := GetRegister( crNoRegister);
                UseRegister( ResReg, IsPush);
              end;
            clMemory:
              Exit;
          end;

          GetReference( CodeTree^.Left, ResReg, Ref);

          LockRegister( ResReg);
          Reg := GetRegister( ResReg);
          UseRegister( Reg, B);
          CodeTree^.Right^.Location.Location := clRegister;
          CodeTree^.Right^.Location.Register := Reg;
          DoExpression( CodeTree^.Right);

          Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
            caiMOV, crESI, Reg)));
          ReleaseRegister( Reg, B);
          UnlockRegister( ResReg);
          Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
            caiMOV, crEDI, ResReg)));
          if CodeTree^.Location.Location = clNone then
             ReleaseRegister( ResReg, IsPush);
          CopyObject( pObjectDefinition( CodeTree^.ResType)^.GetVMTname);
        end;

      cSetDefinition:
        begin
          PushUsedRegisters;
          OldUsedRegisters := UsedRegisters;
          OldCounter := Counter;
          Counter := 0;
          UsedRegisters := [];
          case CodeTree^.Location.Location of
            clNone,
            clRegister:
              begin
                IncTempSize( 32);
                CodeTree^.Right^.Location.Location := clMemory;
                CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
                  -CurTempSize-LocalSize, nil, csDefault,
                  CodeTree^.Right^.Location.Reference);
              end;
            clMemory:
              begin
                CodeTree^.Right^.Location := CodeTree^.Location;
              end;
          end;

          DoExpression( CodeTree^.Right);
          Res^.Concat(
            _LEA_( crEAX, CodeTree^.Right^.Location.Reference));
          Res^.Concat(
            _PUSH_( crEAX));

          UseRegister( crEAX, IsPush);
          GetReference( CodeTree^.Left, crEAX, Ref);
          Res^.Concat(
            _PUSH_( crEAX));

          Res^.Concat(
            _PUSH_const( pSetDefinition(CodeTree^.ResType)^.Min ));
          Res^.Concat(
            _PUSH_const( pSetDefinition(CodeTree^.ResType)^.Max ));

          Res^.Concat( New( pAsmInstruction, Create_JSymbol(
            caiCALL, NameSetStore)));

          if Counter <> 0 then
            DecTempSize( Counter);
          Counter := OldCounter;
          if CodeTree^.Location.Location in [ clRegister, clNone] then
            begin
              {DecTempSize( 32);}
              if CodeTree^.Location.Location = clRegister then
                Res^.Concat(
                  _LEA_( CodeTree^.Location.Register,
                    CodeTree^.Right^.Location.Reference));
            end;
          UsedRegisters := OldUsedRegisters;
          PopUsedRegisters;
        end;

      else
        begin
          case CodeTree^.Location.Location of
            clMemory:
              begin
                CodeTree^.Right^.Location.Location := clMemory;
                Reg := CodeTree^.Location.Reference.Base;

                LockRegister( Reg);
                ResReg := GetRegister( Reg);
                UseRegister( ResReg, IsPush);
                GetReference( CodeTree^.Left, ResReg,
                  CodeTree^.Right^.Location.Reference);
                DoExpression( CodeTree^.Right);
                Res^.Concat(
                  _LEA_( crESI, Ref));
                ReleaseRegister( ResReg, IsPush);
                UnlockRegister( Reg);

                Res^.Concat(
                  _LEA_( crEDI, CodeTree^.Location.Reference));
                CopyMemory( CodeTree^.ResType^.GetSize);
              end;
            clRegister:
              begin
                CodeTree^.Right^.Location.Location := clMemory;
                Reg := CodeTree^.Location.Register;
                GetReference( CodeTree^.Left, Reg,
                  CodeTree^.Right^.Location.Reference);
                LockRegister( Reg);
                DoExpression( CodeTree^.Right);
                UnlockRegister( Reg);
              end;
            clNone:
              begin
                ResReg := GetRegister( crNoRegister);
                UseRegister( ResReg, IsPush);
                CodeTree^.Right^.Location.Location := clMemory;
                GetReference( CodeTree^.Left, ResReg,
                  CodeTree^.Right^.Location.Reference);
                LockRegister( ResReg);
                DoExpression( CodeTree^.Right);
                UnlockRegister( ResReg);
                ReleaseRegister( ResReg, IsPush);
              end;
          end;
        end;
    end;
  end;

procedure tCodeGenerator.DoVariable( CodeTree: pCodeTree);
  var
    Ref: tReference;
    OldUsedRegisters: tRegisterSet;
    IsPush: Boolean;
    Reg: tRegister;
    AI: pAsmInstruction;
  begin
    case CodeTree^.ResType^.DefType of
      cOrdDefinition,
      cUserOrdDefinition,
      cPointerDefinition,
      cFunctionTypeDefinition:
        if CodeTree^.Location.Location = clRegister then
          begin
            GetReference( CodeTree, CodeTree^.Location.Register, Ref);
            if Ref.Size <> csDWord then
              begin
                if ( CodeTree^.ResType^.DefType = cOrdDefinition) and
                  ( pOrdDefinition( CodeTree^.ResType)^.BaseType in
                  [cbtInteger, cbtShortInt, cbtLongInt] ) then
                  Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
                    caiMOVSX, CodeTree^.Location.Register, Ref)))
                else
                  Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
                    caiMOVZX, CodeTree^.Location.Register, Ref)))
              end
            else
              Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
                caiMOV, CodeTree^.Location.Register, Ref)));
          end;

      cBooleanDefinition:
        case CodeTree^.Location.Location of
          clRegister:
          begin
            GetReference( CodeTree, CodeTree^.Location.Register, Ref);
            if Ref.Size <> csDWord then
              begin
                Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
                  caiMOVZX, CodeTree^.Location.Register, Ref)))
              end
            else
              Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
                caiMOV, CodeTree^.Location.Register, Ref)));
          end;
          clFlags:
            begin
              Reg := GetRegister( crNoRegister);
              UseRegister( Reg, IsPush);
              GetReference( CodeTree, Reg, Ref);
              Res^.Concat( New( pAsmInstruction, Create_Ref_Const(
                caiCMP, Ref, 0)));
              ReleaseRegister( Reg, IsPush);
              CodeTree^.Location.ResultFlag := cfNotEqual;
              if Assigned( CodeTree^.Location.LabelTrue) then
                begin
                  Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                    caiJNZ, CodeTree^.Location.LabelTrue^)));
                  Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                    caiJMP, CodeTree^.Location.LabelFalse^)));
                end;
            end;
        end;

      cRealDefinition:
        begin
          Reg := GetRegister( crNoRegister);
          UseRegister( Reg, IsPush);
          GetReference( CodeTree, Reg, Ref);
          case CodeTree^.Location.Location of
            clFPUStack:
              if CodeTree^.Location.Register in [ crST, crST0] then
                Res^.Concat( New( pAsmInstruction, Create_Ref(
                  caiFLD, Ref)))
              else
                Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
                  caiFLD, CodeTree^.Location.Register, Ref)));
          end;
          ReleaseRegister( Reg, IsPush);
        end;

      cStringDefinition:
        begin
          case CodeTree^.Location.Location of

            clRegister:
              begin
                GetReference( CodeTree, CodeTree^.Location.Register, Ref);
              end;

            clMemory:
              begin
                PushUsedRegisters;
                OldUsedRegisters := UsedRegisters;
                UsedRegisters := [];

                Res^.Concat(
                  _LEA_( crEAX, CodeTree^.Location.Reference));
                Res^.Concat(
                  _PUSH_( crEAX));

                UseRegister( crEAX, IsPush);
                GetReference( CodeTree, crEAX, Ref);
                Res^.Concat(
                  _PUSH_( crEAX));

                Res^.Concat(
                  _PUSH_const( CodeTree^.ResType^.GetSize - 1));

                Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                  caiCALL, NameStrCopy)));

                UsedRegisters := OldUsedRegisters;
                PopUsedRegisters;
              end;

          end;
        end;

      cObjectDefinition:
        case CodeTree^.Location.Location of
          clRegister:
            GetReference( CodeTree, CodeTree^.Location.Register, Ref);
        end;

      cSetDefinition:
        case CodeTree^.Location.Location of
          clRegister:
            begin
              GetReference( CodeTree, CodeTree^.Location.Register, Ref);
            end;
          clMemory:
          begin
            PushUsedRegisters;
            OldUsedRegisters := UsedRegisters;
            UsedRegisters := [];

            Res^.Concat(
              _LEA_( crEAX, CodeTree^.Location.Reference));
            Res^.Concat(
              _PUSH_( crEAX));

            UseRegister( crEAX, IsPush);
            GetReference( CodeTree, crEAX, Ref);
            Res^.Concat(
              _PUSH_( crEAX));
            Res^.Concat(
              _PUSH_const( pSetDefinition(CodeTree^.ResType)^.Min ));
            Res^.Concat(
              _PUSH_const( pSetDefinition(CodeTree^.ResType)^.Max ));
            Res^.Concat( New( pAsmInstruction, Create_JSymbol(
              caiCALL, NameSetLoad)));

            UsedRegisters := OldUsedRegisters;
            PopUsedRegisters;

          end;
        end;
      else
        begin
          case CodeTree^.Location.Location of
            clRegister:
              begin
                GetReference( CodeTree, CodeTree^.Location.Register, Ref);
              end;
            clMemory:
              begin
                Reg := GetRegister( CodeTree^.Location.Reference.Base);
                UseRegister( Reg, IsPush);
                GetReference( CodeTree, Reg, Ref);
                Res^.Concat(
                  _LEA_( crESI, Ref));
                ReleaseRegister( Reg, IsPush);

                Res^.Concat(
                  _LEA_( crEDI, CodeTree^.Location.Reference));
                CopyMemory( CodeTree^.ResType^.GetSize);
              end;
          end;
        end;
    end;
  end;

procedure tCodeGenerator.DoTypeConversion( CodeTree: pCodeTree);
  var
    Ref: tReference;
    Reg: tRegister;
    IsPush: Boolean;
  begin
    case CodeTree^.Node.Conversion of

      ccChar_2_String:
        if CodeTree^.Location.Location = clMemory then
          begin
            CodeTree^.Left^.Location.Location := clRegister;
            Reg := GetRegister( crNoRegister);
            UseRegister( Reg, IsPush);
            CodeTree^.Left^.Location.Register := Reg;
            DoExpression( CodeTree^.Left);
            CodeTree^.Location.Reference.Size := csByte;
            Res^.Concat( New( pAsmInstruction, Create_Ref_Const( caiMOV,
              CodeTree^.Location.Reference, 1)));
            Inc( CodeTree^.Location.Reference.Offset);
            Res^.Concat( New( pAsmInstruction, Create_Ref_Reg( caiMOV,
              CodeTree^.Location.Reference, GetReg( Reg, csByte))));
            Dec( CodeTree^.Location.Reference.Offset);
            ReleaseRegister( Reg, IsPush);
        end;

      cc8Bit_2_Real,
      cc16Bit_2_Real,
      cc32Bit_2_Real:
        if CodeTree^.Location.Location = clFPUStack then
          begin
          case CodeTree^.Left^.Node.CodeType of
            cctIntConst:
              DoLoadIntConstToFpuStack( CodeTree^.Left);
            else
              begin
                Reg := GetRegister( crNoRegister);
                UseRegister( Reg, IsPush);
                CodeTree^.Left^.Location.Location := clRegister;
                CodeTree^.Left^.Location.Register := Reg;
                DoExpression( CodeTree^.Left);
                Res^.Concat(
                  _PUSH_( Reg));
                CreateReference( crDefaultSeg, crESP, crNoRegister, 1, 0, nil, csDWord, Ref);
                Res^.Concat( New( pAsmInstruction, Create_Ref(
                  caiFILD, Ref)));
                Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                  caiADD, crESP, 4)));
                ReleaseRegister( Reg, IsPush);
              end;
          end;
        end;

      cc16bit_2_8bit,
      cc32bit_2_8bit,
      cc32bit_2_16bit:
        begin
          CodeTree^.Left^.Location := CodeTree^.Location;
          CodeTree^.Left^.ResType := CodeTree^.ResType;
          DoExpression( CodeTree^.Left);
        end;

      cc8bit_2_16bit,
      cc8bit_2_32bit,
      cc16bit_2_32bit:
        begin
          CodeTree^.Left^.Location := CodeTree^.Location;
          DoExpression( CodeTree^.Left);
        end;

      else
        begin
          if (CodeTree^.Location.Location = clFlags) then
            begin
              if (CodeTree^.Left^.ResType^.DefType <> cBooleanDefinition) then
                begin
                  Reg := GetRegister( crNoRegister);
                  UseRegister( Reg, IsPush);
                  CodeTree^.Left^.Location.Location := clRegister;
                  CodeTree^.Left^.Location.Register := Reg;
                end
              else
                CodeTree^.Left^.Location := CodeTree^.Location;
              DoExpression( CodeTree^.Left);
              case CodeTree^.Left^.ResType^.DefType of
                cBooleanDefinition:
                  CodeTree^.Location.ResultFlag := CodeTree^.Left^.Location.ResultFlag;
                cOrdDefinition,
                cUserOrdDefinition,
                cPointerDefinition:
                  begin
                    Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                      caiOR, GetReg( Reg, GetSize( CodeTree^.ResType^.GetSize)),
                      GetReg( Reg, GetSize( CodeTree^.ResType^.GetSize)) )));
                    ReleaseRegister( Reg, IsPush);
                    CodeTree^.Location.ResultFlag := cfNotEqual;
                  end;
                else
                  begin
                    CreateReference( crDefaultSeg, Reg, crNoRegister, 1, 0, nil,
                      GetSize( CodeTree^.ResType^.GetSize), Ref);
                    Res^.Concat( New( pAsmInstruction, Create_Ref_Const(
                      caiCMP, Ref, 0)));
                    ReleaseRegister( Reg, IsPush);
                    CodeTree^.Location.ResultFlag := cfNotEqual;
                  end;
              end;
              if Assigned( CodeTree^.Location.LabelTrue) then
                begin
                  Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                    GetJUMP( CodeTree^.Location.ResultFlag), CodeTree^.Location.LabelTrue^)));
                  Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                    caiJMP, CodeTree^.Location.LabelFalse^)));
                end;
            end
          else if Assigned( CodeTree^.Left^.ResType) and
              (CodeTree^.Left^.ResType^.DefType = cBooleanDefinition) then
            begin
              CodeTree^.Left^.Location.Location := clFlags;
              DoExpression( CodeTree^.Left);
              case CodeTree^.Location.Location of
                clRegister:
                  begin
                    Reg := CodeTree^.Location.Register;
                    Res^.Concat( New( pAsminstruction, Create_Reg(
                      GetSET( CodeTree^.Left^.Location.ResultFlag),
                      GetReg( Reg, csByte) )));
                    Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                      caiMOVZX, Reg, GetReg( Reg, csByte) )));
                  end;
                clMemory:
                  begin
                    Ref := CodeTree^.Location.Reference;
                    Ref.Size := csByte;
                    Res^.Concat( New( pAsmInstruction, Create_Ref(
                      GetSET( CodeTree^.Left^.Location.ResultFlag),
                      Ref)));
                  end;
              end;
            end
          else
            begin
              CodeTree^.Left^.Location := CodeTree^.Location;
              if (CodeTree^.Left^.Node.CodeType <> cctAddition) and
                (CodeTree^.Left^.Node.CodeType <> cctSubtraction) and
                (CodeTree^.ResType^.DefType <> cPointerDefinition) then
                CodeTree^.Left^.ResType := CodeTree^.ResType;
              DoExpression( CodeTree^.Left);
            end;
        end;
    end;
  end;

procedure tCodeGenerator.GetReference( CodeTree: pCodeTree; Register: tRegister; var Ref: tReference);
  begin
  end;

procedure tCodeGenerator.DoLoadValue( CodeTree: pCodeTree);
  var
    Ref: tReference;
    AsmOp: tAsmOp;
    IsPush: Boolean;
    AI: pAsmInstruction;
    OldUsedRegisters: tRegisterSet;
  begin
    DoVariable( CodeTree);
  end;

procedure tCodeGenerator.DoDeref( CodeTree: pCodeTree);
  var
    Ref: tReference;
    AsmOp: tAsmOp;
  begin
    DoVariable( CodeTree);
  end;

procedure tCodeGenerator.DoFunctionCall( CodeTree: pCodeTree);
  var
    OldUsedRegisters: tRegisterSet;
    Size: LongInt;
    Ref: tReference;
    OldCounter: LongInt;
    IsPush: Boolean;
    CallType: tCallType;
    I: Integer;
  begin
    OldCounter := Counter;
    Counter := 0;
    {if CodeTree^.Location.Location = clRegister then
      ReleaseRegister( CodeTree^.Location.Register, False);}
    PushUsedRegisters;
    OldUsedRegisters := UsedRegisters;
    UsedRegisters := [];
    Size := 0;
    if Assigned( CodeTree^.ResType) and
      ( CodeTree^.ResType^.DefType in [cRecordDefinition,
      cArrayDefinition, cStringDefinition]) then
      begin
        if (CodeTree^.Location.Location <> clMemory) then
          begin
            Size := CodeTree^.ResType^.GetSize;
            if Size and 3 <> 0 then
              Size := Size and not 3 + 4;
            if CodeTree^.ResType^.DefType = cStringDefinition then
              Size := 256;
            IncTempSize( Size);
            Inc( OldCounter, Size);
            CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
              -LocalSize - CurTempSize,
              nil, csDWord, Ref);
            Res^.Concat(
              _LEA_( crEAX, Ref));
          end
        else
          Res^.Concat(
            _LEA_( crEAX, CodeTree^.Location.Reference));
        Res^.Concat(
          _PUSH_( crEAX));
      end;

    if Assigned( CodeTree^.Node.SelfCode) then
      begin
        UseRegister( crEBX, IsPush);
        CodeTree^.Node.SelfCode^.Location.Location := clRegister;
        CodeTree^.Node.SelfCode^.Location.Register := crEBX;
        DoExpression( CodeTree^.Node.SelfCode);
        if (CodeTree^.Left^.Node.CodeType = cctFunction) and
          (CodeTree^.Left^.Node.FuncSym^.Definition^.ProcOptions and
            poVirtualMethod = 0) then
          ReleaseRegister( crEBX, False)
        else
          LockRegister( crEBX);
        if (CodeTree^.Left^.Node.CodeType = cctFunction) and
          (CodeTree^.Left^.Node.FuncSym^.Definition^.ProcOptions and
            poConstructor <> 0) and
          not CodeTree^.Node.InheritedCall then
          begin
            CreateReference( crDefaultSeg, crEBX, crNoRegister, 1, 0, nil,
              csDWord, Ref);
            Res^.Concat( New( pAsmInstruction, Create_Ref_Offset(
              caiMOV, Ref,
              pObjectDefinition( CodeTree^.Node.SelfCode^.Left^.ResType)^.GetVMTname{$IFDEF PPRO}(){$ENDIF}, 0)));
          end;
        Res^.Concat( _PUSH_( crEBX));
      end;

    if CodeTree^.Left^.Node.CodeType = cctFunction then
      CallType := CodeTree^.Left^.Node.FuncSym^.Definition^.CallType
    else
      CallType := pAbstractFunctionDefinition( CodeTree^.Left^.ResType)^.CallType;
    if Assigned( CodeTree^.Right) and ( CodeTree^.Right^.Node.CodeType = cctFunctionParam) then
      DoFunctionParam( CodeTree^.Right, CallType);

    case CodeTree^.Left^.Node.CodeType of
      cctFunction:
        begin
          if (CodeTree^.Left^.Node.FuncSym^.Definition^.ProcOptions and
              poVirtualMethod <> 0) and not CodeTree^.Node.InheritedCall then
            begin
              Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                caiMOV, crEAX,
                  CodeTree^.Left^.Node.FuncSym^.Definition^.VirtualIndex)));
              Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                caiCALL, NameDispatchVirtual)));
              if CodeTree^.Node.CallType = cctCDECL then
                Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                  caiADD, crESP, CodeTree^.Left^.Node.FuncSym^.Definition^.ParamSize)));
              UnlockRegister( crEBX);
              ReleaseRegister( crEBX, False);
            end
          else
            begin
              I := CodeTree^.Left^.Node.FuncSym^.Definition^.LexLevel;
              if I > 1 then
                if LexLevel < I then
                  Res^.Concat( _PUSH_ ( crEBP ))
                else
                  begin
                    IAsm386.CreateReference( crDefaultSeg, crEBP, crNoRegister,
                      1, 8, nil, csDWord, Ref);
                    while I < LexLevel do
                      begin
                        Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
                          caiMOV, crEAX, Ref)));
                        Ref.Base := crEAX;
                        Inc( I);
                      end;
                    Res^.Concat( New( pAsmInstruction, Create_Ref(
                      caiPUSH, Ref)));
                  end;
              Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                caiCALL, CodeTree^.Left^.Node.FuncSym^.AsmName{$IFDEF PPRO}(){$ENDIF} )));
              if CodeTree^.Node.CallType = cctCDECL then
                Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                  caiADD, crESP, CodeTree^.Left^.Node.FuncSym^.Definition^.ParamSize)));
            end;
        end;
      cctVariable:
        begin
          UseRegister( crEBX, IsPush);
          GetReference( CodeTree^.Left, crEBX, Ref);
          Res^.Concat( New( pAsmInstruction, Create_Ref(
            caiCALL, Ref )));
          if CodeTree^.Node.CallType = cctCDECL then
            Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
              caiADD, crESP, pAbstractFunctionDefinition( CodeTree^.Left^.ResType)^.ParamSize)));
          ReleaseRegister( crEBX, IsPush);
        end;
      else
        begin
          CodeTree^.Left^.Location.Location := clRegister;
          CodeTree^.Left^.Location.Register := crEBX;
          UseRegister( crEBX, IsPush);
          DoExpression( CodeTree^.Left);
          Res^.Concat( New( pAsmInstruction, Create_Reg(
            caiCALL, crEBX)));
          if CodeTree^.Node.CallType = cctCDECL then
            Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
              caiADD, crESP, pAbstractFunctionDefinition( CodeTree^.Left^.ResType)^.ParamSize)));
          ReleaseRegister( crEBX, IsPush);
        end;
    end;

    if Assigned( CodeTree^.ResType) then
      if ( CodeTree^.ResType^.DefType in [cRecordDefinition,
        cArrayDefinition, cStringDefinition]) then
        begin
          if (CodeTree^.Location.Location = clRegister) and
            (CodeTree^.Location.Register <> crNoRegister) then
            begin
              CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
                -(CodeTree^.Node.FuncSym^.Definition^.LocalSize + CurTempSize), nil, csDWord, Ref);
              Res^.Concat(
                _LEA_( CodeTree^.Location.Register, Ref));
            end;
          {if CodeTree^.Location.Location <> clMemory then
            DecTempSize( Size);}
        end
      else
      case CodeTree^.Location.Location of
        clRegister:
          if CodeTree^.ResType^.GetSize < 4 then
            Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
              caiMOVZX, CodeTree^.Location.Register,
                GetEAX( GetSize(CodeTree^.ResType^.GetSize)) )))
          else
            if not ( CodeTree^.Location.Register in [crEAX, crNoRegister]) then
            Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
              caiMOV, CodeTree^.Location.Register, crEAX)));
        clFlags:
          begin
            Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
              caiOR, crAL, crAL)));
            CodeTree^.Location.ResultFlag := cfNotEqual;
          end;
      end;
    UsedRegisters := OldUsedRegisters;
    PopUsedRegisters;
    if (CodeTree^.Location.Location = clFlags) and
      Assigned( CodeTree^.Location.LabelTrue) then
      begin
        Res^.Concat( New( pAsmInstruction, Create_JSymbol(
          caiJNZ, CodeTree^.Location.LabelTrue^)));
        Res^.Concat( New( pAsmInstruction, Create_JSymbol(
          caiJMP, CodeTree^.Location.LabelFalse^)));
      end;
    {if CodeTree^.Location.Location = clRegister then
      UseRegister( CodeTree^.Location.Register, IsPush);}
    if Counter > 0 then
      DecTempSize( Counter);
    Counter := OldCounter;
  end;

procedure tCodeGenerator.DoFunctionParam( CodeTree: pCodeTree; CallType: tCallType);
  begin
    case CallType of
      cctPascal:
        begin
          if Assigned( CodeTree^.Left) and ( CodeTree^.Left^.Node.CodeType = cctFunctionParam) then
            DoFunctionParam( CodeTree^.Left, CallType);
          DoPushParam( CodeTree^.Right);
        end;
      cctStdCall,
      cctCDecl:
        begin
          DoPushParam( CodeTree^.Right);
          if Assigned( CodeTree^.Left) and ( CodeTree^.Left^.Node.CodeType = cctFunctionParam) then
            DoFunctionParam( CodeTree^.Left, CallType);
        end;
    end;
  end;

procedure tCodeGenerator.DoPushParam( CodeTree: pCodeTree);
  var
    Register: tRegister;
    IsPush: Boolean;
    Ref: tReference;
    Size: LongInt;
    AI: pAsmInstruction;
    OldUsedRegisters: tRegisterSet;
    LabTrue, LabFalse, LabEnd: String;
  begin
    Register := crEAX;
    IsPush := False;
    case CodeTree^.ResType^.DefType of
      cBooleanDefinition:
        begin
          LabTrue := CurCompiler^.CreateLabel;
          LabFalse := CurCompiler^.CreateLabel;
          LabEnd := CurCompiler^.CreateLabel;
          CodeTree^.Location.Location := clFlags;
          CodeTree^.Location.LabelTrue := NewStr( LabTrue);
          CodeTree^.Location.LabelFalse := NewStr( LabFalse);
          DoExpression( CodeTree);

          Res^.Concat( MakeLabel( New( pAsmInstruction, Create( caiNoInstruction)),
            LabTrue));
          Res^.Concat( _PUSH_const( 1));
          Res^.Concat( New( pAsmInstruction, Create_JSymbol(
            caiJMP, LabEnd)));

          Res^.Concat( MakeLabel( New( pAsmInstruction, Create( caiNoInstruction)),
            LabFalse));
          Res^.Concat( _PUSH_const( 0));

          Res^.Concat( MakeLabel( New( pAsmInstruction, Create( caiNoInstruction)),
            LabEnd));
        end;

      cOrdDefinition,
      cUserOrdDefinition,
      cPointerDefinition,
      cFunctionTypeDefinition:
        begin
          UseRegister( Register, IsPush);
          CodeTree^.Location.Location := clRegister;
          CodeTree^.Location.Register := Register;
          DoExpression( CodeTree);
          if IsPush then
            begin
              CreateReference( crDefaultSeg, crESP, crNoRegister, 1, 0, nil, csDWORD, Ref);
              Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
                caiXCHG, Register, Ref)));
            end
          else
            begin
              Res^.Concat(
                _PUSH_( Register));
            end;
          ReleaseRegister( Register, False);
        end;
      cRealDefinition:
        begin
          CodeTree^.Location.Location := clFPUStack;
          CodeTree^.Location.Register := crST;
          DoExpression( CodeTree);
          Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
            caiSUB, crESP, (CodeTree^.ResType^.GetSize{$IFDEF PPRO}(){$ENDIF} + 3) and not 3)));
          CreateReference( crDefaultSeg, crESP, crNoRegister, 1, 0,
            nil, GetSize(CodeTree^.ResType^.GetSize{$IFDEF PPRO}(){$ENDIF}), Ref);
          Res^.Concat( New( pAsmInstruction, Create_Ref(
            caiFSTP, Ref)));
        end;
      cStringDefinition:
        {if not (CodeTree^.Node.CodeType in [ cctVariable, cctDeref,
          cctLoadValue, cctWithSymbol, cctIntConst]) then
          begin
            CodeTree^.Location.Location := clMemory;
            IncTempSize( 256);
            CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
              -CurTempSize-LocalSize, nil, csDefault,
              CodeTree^.Location.Reference);
            DoExpression( CodeTree);
            Res^.Concat(
              _LEA_( crESI, CodeTree^.Location.Reference));
            CreateReference( crDefaultSeg, crESI, crNoRegister, 1, 0, nil, csByte, Ref);
            Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
              caiMOVZX, crECX, Ref)));

            Size := CodeTree^.ResType^.GetSize;
            if Size and 3 <> 0 then Size := Size and not 3 + 4;
            Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
              caiSUB, crESP, Size)));
            CreateReference( crDefaultSeg, crESP, crNoRegister, 1, 0, nil, csDefault, Ref);
            Res^.Concat(
              _LEA_( crEDI, Ref));
            Res^.Concat( New( pAsmInstruction, Create_Reg( caiINC, crECX)));
            Res^.Concat( New( pAsmInstruction, Create( caiCLD)));
            AI := New( pAsmInstruction, Create( caiMOVSB));
            AI^.Prefix := caiREP;
            Res^.Concat( AI);
          end
        else}
          begin
            CodeTree^.Location.Location := clMemory;
            IncTempSize( 256);
            CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
              -CurTempSize-LocalSize, nil, csDefault,
              CodeTree^.Location.Reference);
            DoExpression( CodeTree);
            Res^.Concat(
              _LEA_( crESI, CodeTree^.Location.Reference));
            Res^.Concat( _PUSH_( crESI));

            {Size := CodeTree^.ResType^.GetSize;
            if Size and 3 <> 0 then Size := Size and not 3 + 4;
            Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
              caiSUB, crESP, Size)));
            CreateReference( crDefaultSeg, crESP, crNoRegister, 1, 0,
              nil, csDefault, Ref);
            Res^.Concat(
              _LEA_( crESI, Ref));

            PushUsedRegisters;
            OldUsedRegisters := UsedRegisters;
            UsedRegisters := [];

            Res^.Concat(
              _PUSH_( crESI));

            GetReference( CodeTree, crEAX, Ref);
            Res^.Concat(
              _PUSH_( crEAX));

            Res^.Concat(
              _PUSH_const( CodeTree^.ResType^.GetSize - 1));

            Res^.Concat( New( pAsmInstruction, Create_JSymbol(
              caiCALL, NameStrCopy)));

            UsedRegisters := OldUsedRegisters;
            PopUsedRegisters;}
          end;

      cObjectDefinition:
        begin
          UseRegister( Register, IsPush);
          CodeTree^.Location.Location := clRegister;
          CodeTree^.Location.Register := Register;
          DoExpression( CodeTree);
          Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
            caiMOV, crESI, Register)));
          ReleaseRegister( Register, IsPush);
          Size := CodeTree^.ResType^.GetSize{$IFDEF PPRO}(){$ENDIF};
          if Size and 3 <> 0 then
            Size := Size and not 3 + 4;
          Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
            caiSUB, crESP, Size)));
          CreateReference( crDefaultSeg, crESP, crNoRegister, 1, 0, nil,
            csDefault, Ref);
          Res^.Concat(
            _LEA_( crEDI, Ref));
          CopyObject( pObjectDefinition( CodeTree^.ResType)^.GetVMTname{$IFDEF PPRO}(){$ENDIF});
        end;

      cSetDefinition:
        begin
          Size := CodeTree^.ResType^.GetSize{$IFDEF PPRO}(){$ENDIF};
          if Size and 3 <> 0 then Size := Size and not 3 + 4;
          Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
            caiSUB, crESP, Size)));
          CreateReference( crDefaultSeg, crESP, crNoRegister, 1, 0, nil, csDefault, Ref);
          Res^.Concat(
            _LEA_( crEBX, Ref));

          IncTempSize( 32);
          CodeTree^.Location.Location := clMemory;
          CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
            -CurTempSize-LocalSize, nil, csDefault,
            CodeTree^.Location.Reference);
          UseRegister( crEBX, IsPush);
          LockRegister( crEBX);
          DoExpression( CodeTree);
          UnlockRegister( crEBX);
          ReleaseRegister( crEBX, IsPush);

          Res^.Concat(
            _LEA_( crEAX, CodeTree^.Location.Reference));
          Res^.Concat(
            _PUSH_( crEAX));

          Res^.Concat(
            _PUSH_( crEBX));

          Res^.Concat(
            _PUSH_const( pSetDefinition(CodeTree^.ResType)^.Min ));
          Res^.Concat(
            _PUSH_const( pSetDefinition(CodeTree^.ResType)^.Max ));

          Res^.Concat( New( pAsmInstruction, Create_JSymbol(
            caiCALL, NameSetStore)));

        end;
      else
        begin
          Size := CodeTree^.ResType^.GetSize{$IFDEF PPRO}(){$ENDIF};
          if Size and 3 <> 0 then Size := Size and not 3 + 4;
          Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
            caiSUB, crESP, Size)));
          UseRegister( crEAX, IsPush);
          CreateReference( crDefaultSeg, crESP, crNoRegister, 1, 0,
            nil, csDefault, Ref);
          Res^.Concat(
            _LEA_( crEAX, Ref));
          CodeTree^.Location.Location := clMemory;
          CreateReference( crDefaultSeg, crEAX, crNoRegister, 1, 0, nil,
            csDefault, CodeTree^.Location.Reference);
          LockRegister( crEAX);
          DoExpression( CodeTree);
          UnlockRegister( crEAX);
          ReleaseRegister( crEAX, IsPush);

        end;
    end;
  end;

procedure tCodeGenerator.DoLoadAddress( CodeTree: pCodeTree);
  var
    Ref: tReference;
    LabTrue, LabFalse, LabEnd: String;
  begin
    if Assigned( CodeTree) and Assigned( CodeTree^.Left) and
      (CodeTree^.Location.Location = clRegister) then
      begin
        case CodeTree^.Left^.Node.CodeType of
          cctLoadValue,
          cctWithSymbol,
          cctVariable,
          cctDeref,
          cctAssignment: if CodeTree^.Location.Register <> crNoRegister then
            begin
              GetReference( CodeTree^.Left, CodeTree^.Location.Register, Ref);
            end;
          cctFunction:
            begin
              Res^.Concat( New( pAsmInstruction, Create_Reg_Offset(
                caiMOV, CodeTree^.Location.Register,
                CodeTree^.Left^.Node.FuncSym^.AsmName{$IFDEF PPRO}(){$ENDIF}, 0 )));
            end;
          cctTypeConversion:
            begin
              case CodeTree^.Left^.Node.Conversion of
                ccChar_2_String:
                  begin
                    IncTempSize( 4);
                    CodeTree^.Left^.Location.Location := clMemory;
                    CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
                      -CurTempSize - LocalSize, nil, csDefault,
                      CodeTree^.Left^.Location.Reference);
                    DoExpression( CodeTree^.Left);
                    Res^.Concat(
                      _LEA_( CodeTree^.Location.Register,
                      CodeTree^.Left^.Location.Reference));
                  end;
                else
                  begin
                    CodeTree^.Left^.Location := CodeTree^.Location;
                    DoLoadAddress( CodeTree^.Left);
                  end;
              end;
            end;

          cctStringConst:
            begin
              CodeTree^.Left^.Location := CodeTree^.Location;
              DoStringConst( CodeTree^.Left);
            end;

          cctPCharConst:
            begin
              CodeTree^.Left^.Location := CodeTree^.Location;
              DoPCharConst( CodeTree^.Left);
            end;

          else
            begin
              case CodeTree^.Left^.ResType^.DefType of
                cBooleanDefinition:
                  begin
                    LabTrue := CurCompiler^.CreateLabel;
                    LabFalse := CurCompiler^.CreateLabel;
                    LabEnd := CurCompiler^.CreateLabel;
                    CodeTree^.Location.Location := clFlags;
                    CodeTree^.Location.LabelTrue := NewStr( LabTrue);
                    CodeTree^.Location.LabelFalse := NewStr( LabFalse);
                    IncTempSize( 4);
                    CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
                      -CurTempSize - LocalSize, nil,
                      csDWord,
                      Ref);
                    DoExpression( CodeTree);

                    Res^.Concat( MakeLabel( New( pAsmInstruction, Create( caiNoInstruction)),
                      LabTrue));
                    Res^.Concat( New( pAsmInstruction, Create_Ref_Const(
                      caiMOV, Ref, 1)));
                    Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                      caiJMP, LabEnd)));

                    Res^.Concat( MakeLabel( New( pAsmInstruction, Create( caiNoInstruction)),
                      LabFalse));
                    Res^.Concat( New( pAsmInstruction, Create_Ref_Const(
                      caiMOV, Ref, 0)));

                    Res^.Concat( MakeLabel( New( pAsmInstruction, Create( caiNoInstruction)),
                      LabEnd));
                    Res^.Concat(
                      _LEA_( CodeTree^.Location.Register, Ref));
                  end;
                cOrdDefinition,
                cPointerDefinition,
                cUserOrdDefinition:
                  begin
                    CodeTree^.Left^.Location := CodeTree^.Location;
                    DoExpression( CodeTree^.Left);
                    IncTempSize( 4);
                    CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
                      -CurTempSize - LocalSize, nil,
                      csDWord,
                      Ref);
                    Res^.Concat( New( pAsmInstruction, Create_Ref_Reg(
                      caiMOV, Ref, CodeTree^.Location.Register)));
                    Res^.Concat(
                      _LEA_( CodeTree^.Location.Register, Ref));
                  end;
                cRealDefinition:
                  begin
                    CodeTree^.Left^.Location.Location := clFPUStack;
                    CodeTree^.Left^.Location.Register := crST;
                    DoExpression( CodeTree^.Left);
                    IncTempSize( 12);
                    CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
                      -CurTempSize - LocalSize, nil,
                      GetSize( CodeTree^.Left^.ResType^.GetSize{$IFDEF PPRO}(){$ENDIF}),
                      Ref);
                    Res^.Concat( New( pAsmInstruction, Create_Ref(
                      caiFSTP, Ref)));
                    Res^.Concat(
                      _LEA_( CodeTree^.Location.Register,
                      Ref));
                  end;
                cStringDefinition:
                  begin
                    IncTempSize( 256);
                    CodeTree^.Left^.Location.Location := clMemory;
                    CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
                      -CurTempSize - LocalSize, nil, csDefault,
                      CodeTree^.Left^.Location.Reference);
                    DoExpression( CodeTree^.Left);
                    Res^.Concat(
                      _LEA_( CodeTree^.Location.Register,
                      CodeTree^.Left^.Location.Reference));
                  end;
                cSetDefinition:
                  begin
                    IncTempSize( 32);
                    CodeTree^.Left^.Location.Location := clMemory;
                    CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
                      -CurTempSize - LocalSize, nil, csDefault,
                      CodeTree^.Left^.Location.Reference);
                    DoExpression( CodeTree^.Left);
                    Res^.Concat(
                      _LEA_( CodeTree^.Location.Register,
                      CodeTree^.Left^.Location.Reference));
                  end;
                else
                  begin
                    IncTempSize( CodeTree^.Left^.ResType^.GetSize);
                    CodeTree^.Left^.Location.Location := clMemory;
                    CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
                      -CurTempSize - LocalSize, nil, csDefault,
                      CodeTree^.Left^.Location.Reference);
                    DoExpression( CodeTree^.Left);
                    Res^.Concat(
                      _LEA_( CodeTree^.Location.Register,
                      CodeTree^.Left^.Location.Reference));
                  end;
              end;
            end;
        end;
      end;
  end;

procedure tCodeGenerator.DoStringConst( CodeTree: pCodeTree);
  var
    TypeDef: pDefinition;
    Sym: pTypedConstSymbol;
    SymName: String[20];
    Ref: tReference;
    IsPush: Boolean;
    AI: pAsmInstruction;
  begin
    TypeDef := New( pStringDefinition, Init( Length( CodeTree^.Node.StringValue^)));
    SymName := CurCompiler^.CreateLabel;
    Sym := New( pTypedConstSymbol, Init( SymName, TypeDef, 0));
    Sym^.Value.StringValue := NewStr( CodeTree^.Node.StringValue^);
    Sym^.Value.ValueType := cvStringValue;
    CurCompiler^.GlobalSymbols^.Insert( Sym);
    CreateReference( crDefaultSeg, crNoRegister, crNoRegister, 1, 0,
      NewStr(Sym^.AsmName), csByte, Ref);
    case CodeTree^.Location.Location of
      clRegister:
        Res^.Concat(
          _LEA_( CodeTree^.Location.Register, Ref));
      clMemory:
        begin
          Res^.Concat(
            _LEA_( crESI, Ref));
          Res^.Concat(
            _LEA_( crEDI, CodeTree^.Location.Reference));

          IsPush := False;
          if crECX in UsedRegisters then
            begin
              IsPush := True;
              Res^.Concat(
                _PUSH_( crECX));
            end;
          CreateReference( crDefaultSeg, crESI, crNoRegister, 1, 0, nil, csByte, Ref);
          Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
            caiMOVZX, crECX, Ref)));
          Res^.Concat( New( pAsmInstruction, Create_Reg( caiINC, crECX)));
          Res^.Concat( New( pAsmInstruction, Create( caiCLD)));
          AI := New( pAsmInstruction, Create( caiMOVSB));
          AI^.Prefix := caiREP;
          Res^.Concat( AI);
          if IsPush then
            Res^.Concat(
              _POP_( crECX));
        end;
    end;
  end;


procedure tCodeGenerator.DoPCharConst( CodeTree: pCodeTree);
  var
    TypeDef: pDefinition;
    Sym: pTypedConstSymbol;
    SymName: String[20];
    Ref: tReference;
    IsPush: Boolean;
    AI: pAsmInstruction;
  begin
    TypeDef := CodeTree^.ResType;
    SymName := CurCompiler^.CreateLabel;
    Sym := New( pTypedConstSymbol, Init( SymName, TypeDef, 0));
    Sym^.Value.StringValue := NewStr( CodeTree^.Node.StringValue^);
    Sym^.Value.ValueType := cvPCharValue;
    CurCompiler^.GlobalSymbols^.Insert( Sym);
    CreateReference( crDefaultSeg, crNoRegister, crNoRegister, 1, 0,
      NewStr(Sym^.AsmName), csByte, Ref);
    case CodeTree^.Location.Location of
      clRegister:
        Res^.Concat(
          _LEA_( CodeTree^.Location.Register, Ref));
    end;
  end;


procedure tCodeGenerator.DoSetConst( CodeTree: pCodeTree);
  var
    TypeDef: pSetDefinition;
    Sym: pTypedConstSymbol;
    SymName: String[20];
    Ref: tReference;
    OldUsedRegisters: tRegisterSet;
    AI: pAsmInstruction;
  begin
    if (CodeTree^.Location.Location = clMemory) then
    if Assigned( CodeTree^.ResType) and
      Assigned( pSetDefinition(CodeTree^.ResType)^.SetDef) and
      ( pSetDefinition(CodeTree^.ResType)^.SetDef^.DefType <>
        cAbstractDefinition) then
      begin
        TypeDef := New( pSetDefinition, Init(
          pSetDefinition(CodeTree^.ResType)^.SetDef ));
        SymName := CurCompiler^.CreateLabel;
        Sym := New( pTypedConstSymbol, Init( SymName, TypeDef, 0));
        Sym^.Value.ValueType := cvSetValue;
        GetMem( Sym^.Value.InfoPtr, SizeOf( tByteSet));
        Move( CodeTree^.Node.SetValue^, Sym^.Value.InfoPtr^, SizeOf(tByteSet));
        CurCompiler^.GlobalSymbols^.Insert( Sym);

        OldUsedRegisters := UsedRegisters;
        PushUsedRegisters;
        UsedRegisters := [];

        CreateReference( crDefaultSeg, crNoRegister, crNoRegister, 1, 0,
          NewStr(Sym^.AsmName), csByte, Ref);
        Res^.Concat(
          _LEA_( crESI, Ref));

        Res^.Concat(
          _LEA_( crEDI, CodeTree^.Location.Reference));

        Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
          caiMOV, crECX, 8)));
        AI := New( pAsmInstruction, Create( caiMOVSD));
        AI^.Prefix := caiREP;
        Res^.Concat( AI);

        UsedRegisters := OldUsedRegisters;
        PopUsedRegisters;
      end
    else
      begin
        OldUsedRegisters := UsedRegisters;
        PushUsedRegisters;
        UsedRegisters := [];

        Res^.Concat(
          _LEA_( crEDI, CodeTree^.Location.Reference));

        Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
          caiXOR, crEAX, crEAX)));

        Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
          caiMOV, crECX, 8)));
        AI := New( pAsmInstruction, Create( caiSTOSD));
        AI^.Prefix := caiREP;
        Res^.Concat( AI);

        UsedRegisters := OldUsedRegisters;
        PopUsedRegisters;
      end;
  end;

procedure tCodeGenerator.DoSetItem( CodeTree: pCodeTree);
  var
    Ref: tReference;
    OldUsedRegisters: tRegisterSet;
    AI: pAsmInstruction;
  begin
    if CodeTree^.Location.Location = clMemory then
      begin
        OldUsedRegisters := UsedRegisters;
        PushUsedRegisters;
        UsedRegisters := [];

        Res^.Concat(
          _LEA_( crEDI, CodeTree^.Location.Reference));
        Res^.Concat(
          _PUSH_( crEDI));
        Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
          caiMOV, crECX, 8)));
        Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
          caiXOR, crEAX, crEAX)));
        AI := New( pAsmInstruction, Create( caiSTOSD));
        AI^.Prefix := caiREP;
        Res^.Concat( AI);

        CodeTree^.Left^.Location.Location := clRegister;
        CodeTree^.Left^.Location.Register := crEAX;
        DoExpression( CodeTree^.Left);
        Res^.Concat(
          _PUSH_( crEAX));
        Res^.Concat( New( pAsmInstruction, Create_JSymbol(
          caiCALL, NameSetSetItem)));

        UsedRegisters := OldUsedRegisters;
        PopUsedRegisters;
      end;
  end;

procedure tCodeGenerator.DoSetRange( CodeTree: pCodeTree);
  var
    Ref: tReference;
    OldUsedRegisters: tRegisterSet;
    AI: pAsmInstruction;
  begin
    if CodeTree^.Location.Location = clMemory then
      begin
        OldUsedRegisters := UsedRegisters;
        PushUsedRegisters;
        UsedRegisters := [];

        Res^.Concat(
          _LEA_( crEDI, CodeTree^.Location.Reference));
        Res^.Concat(
          _PUSH_( crEDI));
        Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
          caiMOV, crECX, 8)));
        Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
          caiXOR, crEAX, crEAX)));
        AI := New( pAsmInstruction, Create( caiSTOSD));
        AI^.Prefix := caiREP;
        Res^.Concat( AI);

        CodeTree^.Left^.Location.Location := clRegister;
        CodeTree^.Left^.Location.Register := crEAX;
        DoExpression( CodeTree^.Left);
        Res^.Concat(
          _PUSH_( crEAX));

        CodeTree^.Right^.Location.Location := clRegister;
        CodeTree^.Right^.Location.Register := crEAX;
        DoExpression( CodeTree^.Right);
        Res^.Concat(
          _PUSH_( crEAX));

        Res^.Concat( New( pAsmInstruction, Create_JSymbol(
          caiCALL, NameSetSetRange)));

        UsedRegisters := OldUsedRegisters;
        PopUsedRegisters;
      end;
  end;


procedure tCodeGenerator.DoAnd( CodeTree: pCodeTree);
  var
    Ref: tReference;
    Reg, ResReg: tRegister;
    B, IsPush: Boolean;
    ResLabel: String;
    AI: pAsmInstruction;
  begin
    case CodeTree^.ResType^.DefType of
      cBooleanDefinition:
        begin
          ResLabel := CurCompiler^.CreateLabel;

          CodeTree^.Left^.Location.Location := clFlags;
          if Assigned( CodeTree^.Location.LabelTrue) then
            begin
              CodeTree^.Left^.Location.LabelTrue := NewStr( ResLabel);
              CodeTree^.Left^.Location.LabelFalse :=
                CodeTree^.Location.LabelFalse;
            end
          else
            begin
              Reg := GetRegister( crNoRegister);
              UseRegister( Reg, B);
              Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                caiXOR, Reg, Reg )));
            end;
          DoExpression( CodeTree^.Left);
          if not Assigned( CodeTree^.Location.LabelTrue) then
            Res^.Concat( New( pAsmInstruction, Create_Reg(
              GetSET( CodeTree^.Left^.Location.ResultFlag), GetRegL( Reg) )));

          Res^.Concat( MakeLabel( New( pAsmInstruction,
            Create( caiNoInstruction)),
            ResLabel));
          CodeTree^.Right^.Location.Location := clFlags;
          CodeTree^.Right^.Location.LabelTrue :=
            CodeTree^.Location.LabelTrue;
          CodeTree^.Right^.Location.LabelFalse :=
            CodeTree^.Location.LabelFalse;
          DoExpression( CodeTree^.Right);

          CodeTree^.Location.ResultFlag := cfNotEqual;
          if not Assigned( CodeTree^.Location.LabelTrue) then
            begin
              Res^.Concat( New( pAsmInstruction, Create_Reg(
                GetSET( CodeTree^.Left^.Location.ResultFlag), GetRegH( Reg) )));
              Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                caiAND, GetRegL( Reg), GetRegH( Reg) )));
            end;
        end;
      cUserOrdDefinition,
      cOrdDefinition:
        begin
          if pOrdDefinition(CodeTree^.ResType)^.BaseType <> cbtChar then
          if (CodeTree^.Location.Location = clRegister) then
            begin
              CodeTree^.Left^.Location := CodeTree^.Location;
              DoExpression( CodeTree^.Left);
              case CodeTree^.Right^.Node.CodeType of
                cctIntConst:
                  Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                  caiAND, CodeTree^.Location.Register, CodeTree^.Right^.Node.IntValue)));
                else
                  begin
                    LockRegister( CodeTree^.Location.Register);
                    ResReg := GetRegister( CodeTree^.Location.Register);
                    UseRegister( ResReg, IsPush);
                    CodeTree^.Right^.Location.Location := clRegister;
                    CodeTree^.Right^.Location.Register := ResReg;
                    DoExpression( CodeTree^.Right);
                    Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                      caiAND, CodeTree^.Location.Register, ResReg )));
                    ReleaseRegister( ResReg, IsPush);
                    UnlockRegister( CodeTree^.Location.Register);
              end;
          end;
            end;
        end;
    end;
  end;

procedure tCodeGenerator.DoOr( CodeTree: pCodeTree);
  var
    Ref: tReference;
    Reg, ResReg: tRegister;
    B, IsPush: Boolean;
    ResLabel: String;
    AI: pAsmInstruction;
  begin
    case CodeTree^.ResType^.DefType of
      cBooleanDefinition:
        begin
          ResLabel := CurCompiler^.CreateLabel;

          CodeTree^.Left^.Location.Location := clFlags;
          if Assigned( CodeTree^.Location.LabelTrue) then
            begin
              CodeTree^.Left^.Location.LabelTrue :=
                CodeTree^.Location.LabelTrue;
              CodeTree^.Left^.Location.LabelFalse := NewStr( ResLabel);
            end
          else
            begin
              Reg := GetRegister( crNoRegister);
              UseRegister( Reg, IsPush);
              Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                caiXOR, Reg, Reg )));
            end;
          DoExpression( CodeTree^.Left);
          if not Assigned( CodeTree^.Location.LabelTrue) then
            Res^.Concat( New( pAsmInstruction, Create_Reg(
              GetSET( CodeTree^.Left^.Location.ResultFlag), GetRegL( Reg) )));

          Res^.Concat( MakeLabel( New( pAsmInstruction,
            Create( caiNoInstruction)),
            ResLabel));
          CodeTree^.Right^.Location.Location := clFlags;
          CodeTree^.Right^.Location.LabelTrue :=
            CodeTree^.Location.LabelTrue;
          CodeTree^.Right^.Location.LabelFalse :=
            CodeTree^.Location.LabelFalse;
          DoExpression( CodeTree^.Right);

          CodeTree^.Location.ResultFlag := cfNotEqual;
          if not Assigned( CodeTree^.Location.LabelTrue) then
            begin
              Res^.Concat( New( pAsmInstruction, Create_Reg(
                GetSET( CodeTree^.Left^.Location.ResultFlag), GetRegH( Reg) )));
              Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                caiOR, GetRegL( Reg), GetRegH( Reg) )));
            end;
        end;
      cUserOrdDefinition,
      cOrdDefinition:
        begin
          if pOrdDefinition(CodeTree^.ResType)^.BaseType <> cbtChar then
          if CodeTree^.Location.Location = clRegister then
            begin
              CodeTree^.Left^.Location := CodeTree^.Location;
              DoExpression( CodeTree^.Left);
              case CodeTree^.Right^.Node.CodeType of
                cctIntConst:
                  Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                    caiOR, CodeTree^.Location.Register, CodeTree^.Right^.Node.IntValue)));
              else
                begin
                  LockRegister( CodeTree^.Location.Register);
                  ResReg := GetRegister( CodeTree^.Location.Register);
                  UseRegister( ResReg, IsPush);
                  CodeTree^.Right^.Location.Location := clRegister;
                  CodeTree^.Right^.Location.Register := ResReg;
                  DoExpression( CodeTree^.Right);
                  Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                    caiOR, CodeTree^.Location.Register, ResReg )));
                  ReleaseRegister( ResReg, IsPush);
                  UnlockRegister( CodeTree^.Location.Register);
              end;
          end;
            end;
        end;
    end;
  end;

procedure tCodeGenerator.DoXor( CodeTree: pCodeTree);
  var
    Ref: tReference;
    Reg, ResReg: tRegister;
    B, IsPush: Boolean;
    LabTrue, LabFalse, LabEnd: String;
  begin
    case CodeTree^.ResType^.DefType of
      cBooleanDefinition:
        begin
          Reg := GetRegister( crNoRegister);
          UseRegister( Reg, B);

          LabTrue := CurCompiler^.CreateLabel;
          LabFalse := CurCompiler^.CreateLabel;
          LabEnd := CurCompiler^.CreateLabel;
          CodeTree^.Left^.Location.Location := clFlags;
          CodeTree^.Left^.Location.LabelTrue := NewStr( LabTrue);
          CodeTree^.Left^.Location.LabelFalse := NewStr( LabFalse);
          DoExpression( CodeTree^.Left);
          Res^.Concat( MakeLabel( New( pAsmInstruction, Create_Reg_Const(
            caiMOV, GetRegL( Reg), 1 )),
            LabTrue));
          Res^.Concat( New( pAsmInstruction, Create_JSymbol(
            caiJMP, LabEnd)));
          Res^.Concat( MakeLabel( New( pAsmInstruction, Create_Reg_Const(
            caiMOV, GetRegL( Reg), 0 )),
            LabFalse));
          Res^.Concat( MakeLabel( New( pAsmInstruction, Create( caiNoInstruction)),
            LabEnd));
          {Res^.Concat( New( pAsmInstruction, Create_Reg(
            GetSET( CodeTree^.Left^.Location.ResultFlag), GetRegL( Reg) )));}

          LockRegister( Reg);
          LabTrue := CurCompiler^.CreateLabel;
          LabFalse := CurCompiler^.CreateLabel;
          LabEnd := CurCompiler^.CreateLabel;
          CodeTree^.Right^.Location.Location := clFlags;
          CodeTree^.Right^.Location.LabelTrue := NewStr( LabTrue);
          CodeTree^.Right^.Location.LabelFalse := NewStr( LabFalse);
          DoExpression( CodeTree^.Right);
          Res^.Concat( MakeLabel( New( pAsmInstruction, Create_Reg_Const(
            caiMOV, GetRegH( Reg), 1 )),
            LabTrue));
          Res^.Concat( New( pAsmInstruction, Create_JSymbol(
            caiJMP, LabEnd)));
          Res^.Concat( MakeLabel( New( pAsmInstruction, Create_Reg_Const(
            caiMOV, GetRegH( Reg), 0 )),
            LabFalse));
          Res^.Concat( MakeLabel( New( pAsmInstruction, Create( caiNoInstruction)),
            LabEnd));
          {Res^.Concat( New( pAsmInstruction, Create_Reg(
            GetSET( CodeTree^.Left^.Location.ResultFlag), GetRegH( Reg) )));}

          Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
            caiXOR, GetRegL( Reg), GetRegH( Reg) )));

          UnlockRegister( Reg);
          ReleaseRegister( Reg, B);
          CodeTree^.Location.ResultFlag := cfNotEqual;
          if Assigned( CodeTree^.Location.LabelTrue) then
            begin
              Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                caiJNZ, CodeTree^.Location.LabelTrue^)));
              Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                caiJMP, CodeTree^.Location.LabelFalse^)));
            end;
        end;
      cUserOrdDefinition,
      cOrdDefinition:
        begin
          if pOrdDefinition(CodeTree^.ResType)^.BaseType <> cbtChar then
          if CodeTree^.Location.Location = clRegister then
            begin
              CodeTree^.Left^.Location := CodeTree^.Location;
              DoExpression( CodeTree^.Left);
              case CodeTree^.Right^.Node.CodeType of
                cctIntConst:
                  Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                    caiXOR, CodeTree^.Location.Register, CodeTree^.Right^.Node.IntValue)));
              else
                begin
                  LockRegister( CodeTree^.Location.Register);
                  ResReg := GetRegister( CodeTree^.Location.Register);
                  UseRegister( ResReg, IsPush);
                  CodeTree^.Right^.Location.Location := clRegister;
                  CodeTree^.Right^.Location.Register := ResReg;
                  DoExpression( CodeTree^.Right);
                  Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                    caiXOR, CodeTree^.Location.Register, ResReg )));
                  ReleaseRegister( ResReg, IsPush);
                  UnlockRegister( CodeTree^.Location.Register);
              end;
          end;
            end;
        end;
    end;
  end;

procedure tCodeGenerator.DoNot( CodeTree: pCodeTree);
  begin
    case CodeTree^.Location.Location of
      clRegister:
        begin
          CodeTree^.Left^.Location := CodeTree^.Location;
          DoExpression( CodeTree^.Left);
          if CodeTree^.Location.Register <> crNoRegister then
            case CodeTree^.ResType^.DefType of
              cOrdDefinition:
                Res^.Concat( New( pAsmInstruction,  Create_Reg(
                  caiNOT, CodeTree^.Location.Register)));
              cBooleanDefinition:
                begin
                  Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                    caiOR, CodeTree^.Location.Register, CodeTree^.Location.Register)));
                  Res^.Concat( New( pAsmInstruction, Create_Reg(
                    caiSETZ, GetReg( CodeTree^.Location.Register, csByte))));
                end;
            end;
        end;
      clFlags:
        begin
          CodeTree^.Left^.Location.Location := clFlags;
          CodeTree^.Left^.Location.LabelTrue := CodeTree^.Location.LabelFalse;
          CodeTree^.Left^.Location.LabelFalse := CodeTree^.Location.LabelTrue;
          DoExpression( CodeTree^.Left);
          CodeTree^.Location.ResultFlag :=
            FlagNot( CodeTree^.Left^.Location.ResultFlag);
        end;
    end;
  end;

procedure tCodeGenerator.DoNeg( CodeTree: pCodeTree);
  begin
    case CodeTree^.Location.Location of
      clRegister:
        begin
          CodeTree^.Left^.Location := CodeTree^.Location;
          DoExpression( CodeTree^.Left);
          if CodeTree^.Location.Register <> crNoRegister then
            Res^.Concat( New( pAsmInstruction, Create_Reg(
              caiNEG, CodeTree^.Location.Register)));
        end;
      clFPUStack:
        begin
          CodeTree^.Left^.Location := CodeTree^.Location;
          DoExpression( CodeTree^.Left);
          Res^.Concat( New( pAsmInstruction, Create( caiFCHS)));
        end;
    end;
  end;

procedure tCodeGenerator.DoShrShl( var CodeTree: pCodeTree; AC: tAsmOp);
  var
    Ref: tReference;
    ResReg: tRegister;
    IsPush: Boolean;
  begin
    if CodeTree^.Location.Location = clRegister then
      begin
        CodeTree^.Left^.Location := CodeTree^.Location;
        {ResReg := CodeTree^.Location.Register;
        if ResReg = crECX then
          begin
            CodeTree^.Location.Register := GetRegister( crECX);
            UseRegister( CodeTree^.Location.Register, IsPush);
          end;}
        DoExpression( CodeTree^.Left);
        case CodeTree^.ResType^.DefType of
          cUserOrdDefinition,
          cOrdDefinition:
            begin
              case CodeTree^.Right^.Node.CodeType of
                cctIntConst:
                  Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                    AC, CodeTree^.Location.Register, CodeTree^.Right^.Node.IntValue)));
                else
                  begin
                    LockRegister( CodeTree^.Location.Register);
                    if CodeTree^.Location.Register = crECX then
                      ResReg := GetRegister( CodeTree^.Location.Register)
                    else
                      ResReg := crECX;
                    UseRegister( ResReg, IsPush);
                    CodeTree^.Right^.Location.Location := clRegister;
                    CodeTree^.Right^.Location.Register := crECX;
                    DoExpression( CodeTree^.Right);
                    if CodeTree^.Location.Register = crECX then
                      begin
                        Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                          caiXCHG, CodeTree^.Location.Register, ResReg)));
                        Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                          AC, ResReg, crCL)));
                        Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                          caiMOV, CodeTree^.Location.Register, ResReg)));
                      end
                    else
                      Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                        AC, CodeTree^.Location.Register, crCL )));
                    ReleaseRegister( ResReg, IsPush);
                    UnlockRegister( CodeTree^.Location.Register);
                  end;
              end;
            end;
        end;
      end;
  end;


procedure tCodeGenerator.PushSet( CodeTree: pCodeTree);
  var
    Ref: tReference;
  begin
    IncTempSize( 32);
    CodeTree{^.Right}^.Location.Location := clMemory;
    CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
      -CurTempSize - LocalSize, nil, csDefault,
      CodeTree{^.Right}^.Location.Reference);
    DoExpression( CodeTree{^.Right});
    Res^.Concat(
      _LEA_( crEAX, CodeTree{^.Right}^.Location.Reference));
    Res^.Concat(
      _PUSH_( crEAX));
  end;

procedure tCodeGenerator.DoCompare( var CodeTree: pCodeTree; CodeType: tCodeType);
  var
    Ref: tReference;
    Reg, ResReg: tRegister;
    IsPush, B: Boolean;
    AI: tAsmOp;
    AC: pAsmInstruction;
    OldUsedRegisters: tRegisterSet;
    OldCounter: LongInt;
  begin
    case CodeTree^.Left^.ResType^.DefType of
      cBooleanDefinition,
      cPointerDefinition,
      cUserOrdDefinition,
      cOrdDefinition:
        begin
          CodeTree^.Left^.Location.Location := clRegister;
          Reg := GetRegister( crNoRegister);
          UseRegister( Reg, B);
          CodeTree^.Left^.Location.Register := Reg;
          DoExpression( CodeTree^.Left);
          case CodeTree^.Right^.Node.CodeType of
            cctBoolConst,
            cctIntConst,
            cctCharConst,
            cctPointerConst,
            cctOrdConst:
              Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                  caiCMP, Reg, CodeTree^.Right^.Node.IntValue)));
            else
              begin
                LockRegister( Reg);
                ResReg := GetRegister( Reg);
                UseRegister( ResReg, IsPush);
                CodeTree^.Right^.Location.Location := clRegister;
                CodeTree^.Right^.Location.Register := ResReg;
                DoExpression( CodeTree^.Right);
                Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                  caiCMP, Reg, ResReg )));
                ReleaseRegister( ResReg, IsPush);
                UnlockRegister( Reg);
              end;
          end;
          ReleaseRegister( Reg, B);
          if (CodeTree^.Left^.ResType^.DefType = cOrdDefinition) and
            ( pOrdDefinition( CodeTree^.Left^.ResType)^.BaseType in
              [ cbtShortInt, cbtInteger, cbtLongInt]) then
            CodeTree^.Location.ResultFlag :=
              GetSIFlag( CodeType)
          else
            CodeTree^.Location.ResultFlag :=
              GetUIFlag( CodeType);
        end;
      cRealDefinition:
        begin
          CodeTree^.Left^.Location.Location := clFPUStack;
          CodeTree^.Left^.Location.Register := crST;
          DoExpression( CodeTree^.Left);
          CodeTree^.Right^.Location.Location := clFPUStack;
          CodeTree^.Right^.Location.Register := crST;
          DoExpression( CodeTree^.Right);
          Res^.Concat( New( pAsmInstruction, Create( caiFCOMPP)));
          IsPush := False;
          if (crEAX in UsedRegisters) and
            not ((CodeTree^.Location.Location = clRegister) and
            (CodeTree^.Location.Register = crEAX)) then
            begin
              IsPush := True;
              Res^.Concat(
                _PUSH_( crEAX));
            end;
          Res^.Concat( New( pAsmInstruction, Create_Reg(
            caiFSTSW, crAX)));
          Res^.Concat( New( pAsmInstruction, Create( caiFWAIT)));
          Res^.Concat( New( pAsmInstruction, Create( caiSAHF)));
          if IsPush then
            Res^.Concat(
              _POP_( crEAX));
          CodeTree^.Location.ResultFlag := GetFloatFlag( CodeType);
        end;
      cStringDefinition:
        begin
          PushUsedRegisters;
          OldUsedRegisters := UsedRegisters;
          OldCounter := Counter;
          Counter := 0;

          IncTempSize( 256);
          CodeTree^.Left^.Location.Location := clMemory;
          CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
            -CurTempSize - LocalSize, nil, csDefault,
            CodeTree^.Left^.Location.Reference);
          DoExpression( CodeTree^.Left);
          Res^.Concat(
            _LEA_( crEAX, CodeTree^.Left^.Location.Reference));
          Res^.Concat(
            _PUSH_( crEAX));

          IncTempSize( 256);
          CodeTree^.Right^.Location.Location := clMemory;
          CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
            -CurTempSize - LocalSize, nil, csDefault,
            CodeTree^.Right^.Location.Reference);
          DoExpression( CodeTree^.Right);
          Res^.Concat(
            _LEA_( crEAX, CodeTree^.Right^.Location.Reference));
          Res^.Concat(
            _PUSH_( crEAX));

          Res^.Concat( New( pAsmInstruction, Create_JSymbol(
            caiCALL, NameStrCompare)));

          Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
            caiCMP, crEAX, 0)));
          CodeTree^.Location.ResultFlag := GetSIFlag( CodeType);

          if Counter <> 0 then
            DecTempSize( Counter);
          Counter := OldCounter;
          UsedRegisters := OldUsedRegisters;
          PopUsedRegisters;
        end;
      cSetDefinition:
        begin
          OldUsedRegisters := UsedRegisters;
          PushUsedRegisters;
          UsedRegisters := [];
          OldCounter := Counter;
          Counter := 0;

          case CodeType of
            cctEqual:
              begin
                PushSet( CodeTree^.Left);
                PushSet( CodeTree^.Right);
                Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                  caiCALL, NameSetEqual)));
                Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                  caiOR, crAL, crAL)));
                CodeTree^.Location.ResultFlag := cfNotEqual;
              end;
            cctUnequal:
              begin
                PushSet( CodeTree^.Left);
                PushSet( CodeTree^.Right);
                Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                  caiCALL, NameSetEqual)));
                Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                  caiOR, crAL, crAL)));
                CodeTree^.Location.ResultFlag := cfEqual;
              end;
            cctGreaterEq:
              begin
                PushSet( CodeTree^.Left);
                PushSet( CodeTree^.Right);
                Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                  caiCALL, NameSetEqual)));
                Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                  caiOR, crAL, crAL)));
                CodeTree^.Location.ResultFlag := cfNotEqual;
              end;
            cctLessEq:
              begin
                PushSet( CodeTree^.Right);
                PushSet( CodeTree^.Left);
                Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                  caiCALL, NameSetEqual)));
                Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                  caiOR, crAL, crAL)));
                CodeTree^.Location.ResultFlag := cfNotEqual;
              end;
          end;

          if Counter <> 0 then
            DecTempSize( Counter);
          Counter := OldCounter;
          UsedRegisters := OldUsedRegisters;
          PopUsedRegisters;
          {UseRegister( CodeTree^.Location.Register, IsPush);}
        end;
      else
        begin
          Reg := GetRegister( crNoRegister);
          UseRegister( Reg, B);
          CodeTree^.Left^.Location.Location := clRegister;
          CodeTree^.Left^.Location.Register := Reg;
          DoExpression( CodeTree^.Left);
          Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
            caiMOV, crESI, Reg)));

          CodeTree^.Right^.Location.Location := clRegister;
          CodeTree^.Right^.Location.Register := Reg;
          DoExpression( CodeTree^.Right);
          Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
            caiMOV, crEDI, Reg)));
          IsPush := False;
          if (crECX in UsedRegisters) and (Reg <> crECX) then
            begin
              IsPush := True;
              Res^.Concat(
                _PUSH_( crECX));
            end;
          Res^.Concat( New( pAsmInstruction, Create_Reg_Const( caiMOV,
            crECX, CodeTree^.Left^.ResType^.GetSize)));
          AC := New( pAsmInstruction, Create( caiCMPSB));
          AC^.Prefix := caiREP;
          Res^.Concat( AC);
          if IsPush then
            Res^.Concat(
              _POP_( crECX));
          ReleaseRegister( Reg, B);
          CodeTree^.Location.ResultFlag :=
            GetSIFlag( CodeType);
        end;
    end;
    if Assigned( CodeTree^.Location.LabelTrue) then
      begin
        Res^.Concat( New( pAsmInstruction, Create_JSymbol(
          GetJUMP( CodeTree^.Location.ResultFlag), CodeTree^.Location.LabelTrue^)));
        Res^.Concat( New( pAsmInstruction, Create_JSymbol(
          caiJMP, CodeTree^.Location.LabelFalse^)));
      end;
  end;

procedure tCodeGenerator.DoIN( var CodeTree: pCodeTree);
  var
    Ref: tReference;
    ResReg: tRegister;
    IsPush: Boolean;
    AI: tAsmOp;
    OldUsedRegisters: tRegisterSet;
    OldCounter: LongInt;
    LabTrue, LabFalse, LabEnd: String;
  begin
    case CodeTree^.Left^.ResType^.DefType of
      cUserOrdDefinition,
      cOrdDefinition:
        begin
          OldCounter := Counter;
          Counter := 0;
          PushUsedRegisters;
          OldUsedRegisters := UsedRegisters;
          UsedRegisters := [];

          IncTempSize( 32);
          CodeTree^.Right^.Location.Location := clMemory;
          CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
            -CurTempSize - LocalSize, nil, csDefault,
            CodeTree^.Right^.Location.Reference);
          DoExpression( CodeTree^.Right);
          Res^.Concat(
            _LEA_( crEAX, CodeTree^.Right^.Location.Reference));
          Res^.Concat(
            _PUSH_( crEAX));


          CodeTree^.Left^.Location.Location := clRegister;
          CodeTree^.Left^.Location.Register := crEAX;
          DoExpression( CodeTree^.Left);
          Res^.Concat(
            _PUSH_( crEAX));

          Res^.Concat( New( pAsmInstruction, Create_JSymbol(
            caiCALL, NameSetIn)));

          {DecTempSize( 32);}

          Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
            caiOR, crAL, crAL)));
          CodeTree^.Location.ResultFlag := cfNotEqual;
          UsedRegisters := OldUsedRegisters;
          PopUsedRegisters;
          if Assigned( CodeTree^.Location.LabelTrue) then
            begin
              Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                caiJNZ, CodeTree^.Location.LabelTrue^)));
              Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                caiJMP, CodeTree^.Location.LabelFalse^)));
            end;
          if Counter <> 0 then
            DecTempSize( Counter);
          Counter := OldCounter;
        end;
      cBooleanDefinition:
        begin
          OldCounter := Counter;
          Counter := 0;
          PushUsedRegisters;
          OldUsedRegisters := UsedRegisters;
          UsedRegisters := [];

          IncTempSize( 32);
          CodeTree^.Right^.Location.Location := clMemory;
          CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
            -CurTempSize - LocalSize, nil, csDefault,
            CodeTree^.Right^.Location.Reference);
          DoExpression( CodeTree^.Right);
          Res^.Concat(
            _LEA_( crEAX, CodeTree^.Right^.Location.Reference));
          Res^.Concat(
            _PUSH_( crEAX));


          CodeTree^.Left^.Location.Location := clFlags;
          LabTrue := CurCompiler^.CreateLabel;
          LabFalse := CurCompiler^.CreateLabel;
          LabEnd := CurCompiler^.CreateLabel;
          CodeTree^.Left^.Location.LabelTrue := NewStr( LabTrue);
          CodeTree^.Left^.Location.LabelFalse := NewStr( LabFalse);
          ReleaseRegister( crEAX, False);
          DoExpression( CodeTree^.Left);
          Res^.Concat( MakeLabel( _PUSH_const( 1), LabTrue));
          Res^.Concat( New( pAsmInstruction, Create_JSymbol(
            caiJMP, LabEnd)));
          Res^.Concat( MakeLabel( _PUSH_const( 0), LabFalse));
          Res^.Concat( MakeLabel( New( pAsmInstruction, Create(
            caiNoInstruction)), LabFalse));

          Res^.Concat( New( pAsmInstruction, Create_JSymbol(
            caiCALL, NameSetIn)));

          {DecTempSize( 32);}

          Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
            caiOR, crAL, crAL)));
          CodeTree^.Location.ResultFlag := cfNotEqual;
          UsedRegisters := OldUsedRegisters;
          PopUsedRegisters;
          if Assigned( CodeTree^.Location.LabelTrue) then
            begin
              Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                caiJNZ, CodeTree^.Location.LabelTrue^)));
              Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                caiJMP, CodeTree^.Location.LabelFalse^)));
            end;
          if Counter <> 0 then
            DecTempSize( Counter);
          Counter := OldCounter;
        end;
    end;
  end;

procedure tCodeGenerator.DoPred( CodeTree: pCodeTree);
  begin
    if CodeTree^.Location.Location = clRegister then
      begin
        CodeTree^.Left^.Location := CodeTree^.Location;
        DoExpression( CodeTree^.Left);
        Res^.Concat( New( pAsmInstruction, Create_Reg(
          caiDEC, CodeTree^.Location.Register)));
      end;
  end;

procedure tCodeGenerator.DoSucc( CodeTree: pCodeTree);
  begin
    if CodeTree^.Location.Location = clRegister then
      begin
        CodeTree^.Left^.Location := CodeTree^.Location;
        DoExpression( CodeTree^.Left);
        Res^.Concat( New( pAsmInstruction, Create_Reg(
          caiINC, CodeTree^.Location.Register)));
      end;
  end;

procedure tCodeGenerator.DoInc( CodeTree: pCodeTree);
  var
    Ref: tReference;
    ResReg, Reg: tRegister;
    IsPush, B: Boolean;
  begin
    IsPush := False;
    if CodeTree^.Location.Location = clRegister then
      ResReg := CodeTree^.Location.Register
    else
      ResReg := crNoRegister;
    if Assigned( CodeTree^.Right) then
      begin
        if ResReg = crNoRegister then
          begin
            ResReg := GetRegister( crNoRegister);
            UseRegister( ResReg, IsPush);
          end;
        CodeTree^.Right^.Location.Location := clRegister;
        CodeTree^.Right^.Location.Register := ResReg;
        DoExpression( CodeTree^.Right);
        if (CodeTree^.Left^.ResType^.DefType = cPointerDefinition) and
          (pPointerDefinition( CodeTree^.Left^.ResType)^.DefinitionType^.GetSize <> 1) then
          Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
            caiIMUL, ResReg,
            pPointerDefinition( CodeTree^.Left^.ResType)^.DefinitionType^.GetSize)));

        LockRegister( ResReg);
        Reg := GetRegister( ResReg);
        UseRegister( Reg, B);
        GetReference( CodeTree^.Left, Reg, Ref);
        Res^.Concat( New( pAsmInstruction, Create_Ref_Reg( caiADD,
          Ref, GetReg(ResReg, Ref.Size))));
        UnlockRegister( ResReg);
      end
    else
      begin
        Reg := GetRegister( ResReg);
        UseRegister( Reg, B);
        GetReference( CodeTree^.Left, Reg, Ref);
        if (CodeTree^.Left^.ResType^.DefType = cPointerDefinition) and
          (pPointerDefinition( CodeTree^.Left^.ResType)^.DefinitionType^.GetSize <> 1) then
          Res^.Concat( New( pAsmInstruction, Create_Ref_Const(
            caiADD, Ref,
            pPointerDefinition( CodeTree^.Left^.ResType)^.DefinitionType^.GetSize)))
        else
          Res^.Concat( New( pAsmInstruction, Create_Ref( caiINC, Ref)));
      end;
    if (CodeTree^.Location.Location = clRegister) and
      (CodeTree^.Location.Register <> crNoRegister) then
      begin
        if Ref.Size in [csByte, csWord] then
          Res^.Concat( New( pAsmInstruction, Create_Reg_Ref( caiMOVZX,
            CodeTree^.Location.Register, Ref)))
        else
          Res^.Concat( New( pAsmInstruction, Create_Reg_Ref( caiMOV,
            CodeTree^.Location.Register, Ref)));
      end;
    ReleaseRegister( Reg, B);
    if (CodeTree^.Location.Location <> clRegister) or
      (ResReg <> CodeTree^.Location.Register) then
      ReleaseRegister( ResReg, IsPush);
  end;

procedure tCodeGenerator.DoDec( CodeTree: pCodeTree);
  var
    Ref: tReference;
    ResReg, Reg: tRegister;
    IsPush, B: Boolean;
  begin
    IsPush := False;
    if CodeTree^.Location.Location = clRegister then
      ResReg := CodeTree^.Location.Register
    else
      ResReg := crNoRegister;
    if Assigned( CodeTree^.Right) then
      begin
        if ResReg = crNoRegister then
          begin
            ResReg := GetRegister( crNoRegister);
            UseRegister( ResReg, IsPush);
          end;
        CodeTree^.Right^.Location.Location := clRegister;
        CodeTree^.Right^.Location.Register := ResReg;
        DoExpression( CodeTree^.Right);
        LockRegister( ResReg);
        Reg := GetRegister( ResReg);
        if (CodeTree^.Left^.ResType^.DefType = cPointerDefinition) and
          (pPointerDefinition( CodeTree^.Left^.ResType)^.DefinitionType^.GetSize <> 1) then
          Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
            caiIMUL, ResReg,
            pPointerDefinition( CodeTree^.Left^.ResType)^.DefinitionType^.GetSize)));

        UseRegister( Reg, B);
        GetReference( CodeTree^.Left, Reg, Ref);
        Res^.Concat( New( pAsmInstruction, Create_Ref_Reg( caiSUB,
          Ref, GetReg(ResReg, Ref.Size))));
        UnlockRegister( ResReg);
      end
    else
      begin
        Reg := GetRegister( ResReg);
        UseRegister( Reg, B);
        GetReference( CodeTree^.Left, Reg, Ref);
        if (CodeTree^.Left^.ResType^.DefType = cPointerDefinition) and
          (pPointerDefinition( CodeTree^.Left^.ResType)^.DefinitionType^.GetSize <> 1) then
          Res^.Concat( New( pAsmInstruction, Create_Ref_Const(
            caiSUB, Ref,
            pPointerDefinition( CodeTree^.Left^.ResType)^.DefinitionType^.GetSize)))
        else
          Res^.Concat( New( pAsmInstruction, Create_Ref( caiDEC, Ref)));
      end;
    if (CodeTree^.Location.Location = clRegister) and
      (CodeTree^.Location.Register <> crNoRegister) then
      begin
        if Ref.Size in [csByte, csWord] then
          Res^.Concat( New( pAsmInstruction, Create_Reg_Ref( caiMOVZX,
            CodeTree^.Location.Register, Ref)))
        else
          Res^.Concat( New( pAsmInstruction, Create_Reg_Ref( caiMOV,
            CodeTree^.Location.Register, Ref)));
      end;
    ReleaseRegister( Reg, B);
    if (CodeTree^.Location.Location <> clRegister) or
      (ResReg <> CodeTree^.Location.Register) then
      ReleaseRegister( ResReg, IsPush);
  end;

procedure tCodeGenerator.DoLength( CodeTree: pCodeTree);
  var
    Ref: tReference;
    Reg: tRegister;
    IsPush: Boolean;
    OldCounter: LongInt;
  begin
    if CodeTree^.Location.Location = clRegister then
      begin
        OldCounter := Counter;
        Counter := 0;
        case CodeTree^.Left^.Node.CodeType of
          cctVariable,
          cctLoadValue,
          cctWithSymbol,
          cctDeref:
            begin
              Reg := GetRegister( crNoRegister);
              UseRegister( Reg, IsPush);
              GetReference( CodeTree^.Left, Reg, Ref);
              Ref.Size := csByte;
              Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
                caiMOVZX, CodeTree^.Location.Register, Ref)));
              ReleaseRegister( Reg, IsPush);
            end;
          else
            begin
              IncTempSize( 256);
              CodeTree^.Left^.Location.Location := clMemory;
              CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
                -CurTempSize - LocalSize, nil, csDefault,
                CodeTree^.Left^.Location.Reference);
              DoExpression( CodeTree^.Left);
              CodeTree^.Left^.Location.Reference.Size := csByte;
              Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
                caiMOVZX, CodeTree^.Location.Register,
                CodeTree^.Left^.Location.Reference)));
            end;
        end;
        if Counter <> 0 then
          DecTempSize( Counter);
        Counter := OldCounter;
      end;
  end;

procedure tCodeGenerator.DoAssign( CodeTree: pCodeTree);
  var
    Ref: tReference;
    FuncName: pString;
    Reg: tRegister;
    IsPush: Boolean;
    OldCounter: LongInt;
  begin
    OldCounter := Counter;
    Counter := 0;
    UseRegister( crEAX, IsPush);
    GetReference( CodeTree^.Left, crEAX, Ref);
    Res^.Concat(
      _PUSH_( crEAX));

    case CodeTree^.Right^.Node.CodeType of
      cctVariable,
      cctLoadValue,
      cctWithSymbol:
        begin
          GetReference( CodeTree^.Right, crEAX, Ref);
        end;
      cctStringConst:
        begin
          CodeTree^.Right^.Location.Location := clRegister;
          CodeTree^.Right^.Location.Register := crEAX;
          DoStringConst( CodeTree^.Right);
        end;
      else
        begin
          IncTempSize( 256);
          CodeTree^.Right^.Location.Location := clMemory;
          CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
            -CurTempSize -LocalSize, nil, csDefault,
            CodeTree^.Right^.Location.Reference);
          DoExpression( CodeTree^.Right);
          Res^.Concat(
            _LEA_( crEAX, CodeTree^.Right^.Location.Reference));
          {DecTempSize( 256);}
        end;
    end;
    Res^.Concat(
      _PUSH_( crEAX));

    case pFileDefinition( CodeTree^.Left^.ResType)^.FileType of
      cftTextFile:
        FuncName := @NameAssignText;
      cftTyped:
        begin
          if not Assigned( pFileDefinition( CodeTree^.Left^.ResType)^.FileDef) then
            CurCompiler^.Error( erInternalError, 0, 0, '');
          Res^.Concat(
            _PUSH_const(
            pFileDefinition( CodeTree^.Left^.ResType)^.FileDef^.GetSize{$IFDEF PPRO}(){$ENDIF}));
          FuncName := @NameAssignTyped;
        end;
      else
        FuncName := @NameAssignUntyped;
    end;
    Res^.Concat( New( pAsmInstruction, Create_JSymbol(
      caiCALL, FuncName^)));
    ReleaseRegister( crEAX, IsPush);
    if Counter <> 0 then
      DecTempSize( Counter);
    Counter := OldCounter;
  end;


procedure tCodeGenerator.DoWrite( CodeTree: pCodeTree);
  var
    CurCode: pCodeTree;
    FuncName: pString;
    IsPush: Boolean;
    OldCounter: LongInt;
  begin
    if CodeTree^.Location.Location = clNone then
      begin
        CurCode := CodeTree^.Right;
        CodeTree^.Left^.Location.Location := clRegister;
        CodeTree^.Left^.Location.Register := crEAX;
        UseRegister( crEAX, IsPush);
        DoExpression( CodeTree^.Left);
        ReleaseRegister( crEAX, False);
        case pFileDefinition( CodeTree^.Left^.ResType)^.FileType of
          cftTextFile:
            begin
              while Assigned( CurCode) do
                begin
                  OldCounter := Counter;
                  Counter := 0;
                  if Assigned( CurCode^.Left) or
                    (CodeTree^.Node.CodeType = cctWriteLn) then
                    Res^.Concat(
                      _PUSH_( crEAX));

                  Res^.Concat(
                    _PUSH_( crEAX));

                  DoPushParam( CurCode^.Right);
                  DoPushParam( CurCode^.Node.Len);
                  case CurCode^.ResType^.DefType of
                    cOrdDefinition:
                      begin
                        case pOrdDefinition( CurCode^.ResType)^.BaseType of
                          cbtChar:
                            FuncName := @NameWriteChar;
                          cbtByte, cbtWord, cbtDWord:
                            FuncName := @NameWriteUInt;
                          else
                            FuncName := @NameWriteSInt;
                        end;
                      end;
                    cRealDefinition:
                      begin
                        DoPushParam( CurCode^.Node.Digs);
                        FuncName := @NameWriteReal;
                      end;
                    cPointerDefinition:
                      FuncName := @NameWriteString;
                    cBooleanDefinition:
                      FuncName := @NameWriteBoolean;
                  end;

                  Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                    caiCALL, FuncName^)));

                  if Counter <> 0 then
                    DecTempSize( Counter);
                  Counter := OldCounter;

                  if Assigned( CurCode^.Left) or
                    (CodeTree^.Node.CodeType = cctWriteLn) then
                    Res^.Concat(
                      _POP_( crEAX));

                  CurCode := CurCode^.Left;
                end;

              if CodeTree^.Node.CodeType = cctWriteLn then
                begin
                  Res^.Concat(
                    _PUSH_( crEAX));
                  Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                    caiCALL, NameWriteLine)));
                end;
            end;

          cftTyped:
            begin
              while Assigned( CurCode) do
                begin
                  if Assigned( CurCode^.Left) then
                    Res^.Concat(
                      _PUSH_( crEAX));

                  Res^.Concat(
                    _PUSH_( crEAX));

                  DoPushParam( CurCode^.Right);

                  Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                    caiCALL, NameWriteRecord)));

                  if Assigned( CurCode^.Left) then
                    Res^.Concat(
                      _POP_( crEAX));

                  CurCode := CurCode^.Left;
                end;
            end;

        end;
      end;
  end;

procedure tCodeGenerator.DoRead( CodeTree: pCodeTree);
  var
    CurCode: pCodeTree;
    FuncName: pString;
    Ref: tReference;
    IsPush: Boolean;
  begin
    if CodeTree^.Location.Location = clNone then
      begin
        CurCode := CodeTree^.Right;
        CodeTree^.Left^.Location.Location := clRegister;
        CodeTree^.Left^.Location.Register := crEAX;
        UseRegister( crEAX, IsPush);
        DoExpression( CodeTree^.Left);
        ReleaseRegister( crEAX, IsPush);
        case pFileDefinition( CodeTree^.Left^.ResType)^.FileType of
          cftTextFile:
            begin
              while Assigned( CurCode) do
                begin
                  if Assigned( CurCode^.Left) or
                    (CodeTree^.Node.CodeType = cctReadLn) then
                    Res^.Concat(
                      _PUSH_( crEAX));

                  Res^.Concat(
                    _PUSH_( crEAX));

                  case CurCode^.Right^.ResType^.DefType of
                    cOrdDefinition:
                      begin
                        case pOrdDefinition( CurCode^.ResType)^.BaseType of
                          cbtChar:
                            FuncName := @NameReadChar;
                          else
                            FuncName := @NameReadInt;
                        end;
                        Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                          caiCALL, FuncName^)));
                        UseRegister( crEAX, IsPush);
                        UseRegister( crEBX, IsPush);
                        GetReference( CurCode^.Right, crEBX, Ref);
                        Res^.Concat( New( pAsmInstruction, Create_Ref_Reg(
                          caiMOV, Ref, GetReg( crEAX, Ref.Size) )));
                        ReleaseRegister( crEBX, IsPush);
                        ReleaseRegister( crEAX, IsPush);
                      end;
                    cRealDefinition:
                      begin
                        Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                          caiCALL, NameReadReal)));
                        UseRegister( crEAX, IsPush);
                        GetReference( CurCode^.Right, crEAX, Ref);
                        Res^.Concat( New( pAsmInstruction, Create_Ref(
                          caiFSTP, Ref )));
                        ReleaseRegister( crEAX, IsPush);
                      end;
                    cStringDefinition:
                      begin
                        UseRegister( crEAX, IsPush);
                        GetReference( CurCode^.Right, crEAX, Ref);
                        Res^.Concat(
                          _PUSH_( crEAX));
                        ReleaseRegister( crEAX, IsPush);
                        Res^.Concat(
                          _PUSH_const(
                          pStringDefinition( CurCode^.Right^.ResType)^.Length));
                        Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                          caiCALL, NameReadString)));
                      end;
                    cBooleanDefinition:
                      begin
                        Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                          caiCALL, NameReadBoolean)));
                        UseRegister( crEAX, IsPush);
                        UseRegister( crEBX, IsPush);
                        GetReference( CurCode^.Right, crEBX, Ref);
                        Res^.Concat( New( pAsmInstruction, Create_Ref_Reg(
                          caiMOV, Ref, GetReg( crEAX, Ref.Size) )));
                        ReleaseRegister( crEBX, IsPush);
                        ReleaseRegister( crEAX, IsPush);
                    end;
                  end;

                  if Assigned( CurCode^.Left) or
                    (CodeTree^.Node.CodeType = cctReadLn) then
                    Res^.Concat(
                      _POP_( crEAX));

                  CurCode := CurCode^.Left;
                end;

              if CodeTree^.Node.CodeType = cctReadLn then
                begin
                  Res^.Concat(
                    _PUSH_( crEAX));
                  Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                    caiCALL, NameReadLine)));
                end;
            end;

          cftTyped:
            begin
              while Assigned( CurCode) do
                begin
                  if Assigned( CurCode^.Left) then
                    Res^.Concat(
                      _PUSH_( crEAX));

                  Res^.Concat(
                    _PUSH_( crEAX));

                  UseRegister( crEAX, IsPush);
                  GetReference( CurCode^.Right, crEAX, Ref);
                  Res^.Concat(
                    _PUSH_( crEAX));

                  Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                    caiCALL, NameReadRecord)));

                  if Assigned( CurCode^.Left) then
                    Res^.Concat(
                      _POP_( crEAX));

                  CurCode := CurCode^.Left;
                end;
            end;

        end;
      end;
  end;


procedure tCodeGenerator.DoArithmeticFunction( CodeTree: pCodeTree);
  var
    pS: pString;
    Reg: tRegister;
    IsPush: Boolean;
  begin
    case CodeTree^.Location.Location of
      clFPUStack:
        begin
          CodeTree^.Left^.Location := CodeTree^.Location;
          DoExpression( CodeTree^.Left);
          case CodeTree^.Node.SysSymbolType of
            csstAbs:
              Res^.Concat( New( pAsmInstruction, Create(
                caiFABS)));
            csstSin:
              Res^.Concat( New( pAsmInstruction, Create(
                caiFSIN)));
            csstCos:
              Res^.Concat( New( pAsmInstruction, Create(
                caiFCOS)));
            csstArcTan:
              begin
                Res^.Concat( New( pAsmInstruction, Create(
                  caiFLD1)));
                Res^.Concat( New( pAsmInstruction, Create(
                  caiFPATAN)));
              end;
            csstSqrt:
              Res^.Concat( New( pAsmInstruction, Create(
                caiFSQRT)));
            csstSqr:
              Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                caiFMUL, crST, crST0)));
            csstTan:
              begin
                Res^.Concat( New( pAsmInstruction, Create(
                  caiFSINCOS)));
                Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                  caiFDIVP, crST1, crST)));
              end;
            csstCotan:
              begin
                Res^.Concat( New( pAsmInstruction, Create(
                  caiFSINCOS)));
                Res^.Concat( New( pAsmInstruction, Create(
                  caiFDIV)));
              end;
          end;
        end;

      clFlags:
        begin
          case CodeTree^.Node.SysSymbolType of
            csstODD:
              begin
                Reg := GetRegister( crNoRegister);
                UseRegister( Reg, IsPush);
                CodeTree^.Left^.Location.Location := clRegister;
                CodeTree^.Left^.Location.Register := Reg;
                DoExpression( CodeTree^.Left);
                Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                  caiAND, Reg, 1)));
                ReleaseRegister( Reg, IsPush);
                if Assigned( CodeTree^.Location.LabelTrue) then
                  begin
                    Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                      caiJNZ, CodeTree^.Location.LabelTrue^)));
                    Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                      caiJMP, CodeTree^.Location.LabelFalse^)));
                  end;
                CodeTree^.Location.ResultFlag := cfNotEqual;
              end;
          end;
        end;

      clRegister:
        begin
          CodeTree^.Left^.Location := CodeTree^.Location;
          DoExpression( CodeTree^.Left);
          case CodeTree^.Node.SysSymbolType of
            csstODD:
              begin
                Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                  caiAND, CodeTree^.Location.Register, 1)));
                {Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                  caiXOR, CodeTree^.Location.Register, 1)));}
              end;
            csstAbs:
              begin
                pS := NewStr( CurCompiler^.CreateLabel{$IFDEF PPRO}(){$ENDIF});
                Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
                  caiOR, CodeTree^.Location.Register, CodeTree^.Location.Register)));
                Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                  caiJNS, pS^)));
                Res^.Concat( New( pAsmInstruction, Create_Reg(
                  caiNEG, CodeTree^.Location.Register)));
                Res^.Concat( MakeLabel( New( pAsmInstruction, Create( caiNoInstruction)),
                  pS^));
                DisposeStr( pS);
              end;
          end;
        end;
    end;
  end;


procedure tCodeGenerator.DoNewDispose( CodeTree: pCodeTree);
  var
    Reg: tRegister;
    OldUsedRegisters: tRegisterSet;
    Ref: tReference;
    Name: pString;
    IsPush: Boolean;
    OldCounter: LongInt;
  begin
    if CodeTree^.Location.Location = clRegister then
      begin
        Reg := CodeTree^.Location.Register;
        ReleaseRegister( Reg, False);
      end
    else
      Reg := crEAX;
    OldUsedRegisters := UsedRegisters;
    PushUsedRegisters;
    UsedRegisters := [];
    UseRegister( Reg, IsPush);
    if Assigned( CodeTree^.Left) then
      GetReference( CodeTree^.Left, Reg, Ref)
    else
      begin
        IncTempSize( 4);
        CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
          -LocalSize - CurTempSize, nil, csDefault, Ref);
        Res^.Concat( _LEA_( Reg, Ref));
      end;
    Res^.Concat(
      _PUSH_( Reg));
    if (CodeTree^.Node.CodeType = cctNew) and
      Assigned( CodeTree^.Node.CDcode) then
      Res^.Concat(
        _PUSH_( Reg));

    case CodeTree^.Node.CodeType of
      cctNew:
        begin
          {if Assigned( CodeTree^.Node.CDcode) then
            begin
              CreateReference( crDefaultSeg, Reg, crNoRegister, 1, 0, nil,
                csDWord, Ref);
              Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
                caiMOV, crEAX, Ref)));
              Ref.Base := crEAX;
              Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
                caiMOV, crEAX, Ref)));
              Res^.Concat( New( pAsmInstruction, Create_Ref(
                caiPUSH,  Ref)));
            end
          else}
            Res^.Concat(
              _PUSH_const( pPointerDefinition(CodeTree^.ResType)^.DefinitionType^.GetSize{$IFDEF PPRO}(){$ENDIF} ));
          Name := @NameNew;
        end;
      cctDispose:
        begin
          if Assigned( CodeTree^.Node.CDcode) then
            begin
              CreateReference( crDefaultSeg, Reg, crNoRegister, 1, 0, nil,
                csDWord, Ref);
              Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
                caiMOV, crEBX, Ref)));
              Ref.Base := crEBX;
              Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
                caiMOV, crEAX, Ref)));
              Ref.Base := crEAX;
              Res^.Concat( New( pAsmInstruction, Create_Ref(
                caiPUSH,  Ref)));
              Res^.Concat(
                _PUSH_( crEBX));
              if (CodeTree^.Node.CDcode^.Left^.Node.FuncSym^.Definition^.ProcOptions and
                poVirtualMethod <> 0) then
                begin
                  Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                    caiMOV, crEAX,
                      CodeTree^.Node.CDcode^.Left^.Node.FuncSym^.Definition^.VirtualIndex)));
                  Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                    caiCALL, NameDispatchVirtual)));
                end
              else
                Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                  caiCALL, CodeTree^.Node.CDcode^.Left^.Node.FuncSym^.AsmName{$IFDEF PPRO}(){$ENDIF} )))
            end
          else
            Res^.Concat(
              _PUSH_const( pPointerDefinition(CodeTree^.Left^.ResType)^.DefinitionType^.GetSize{$IFDEF PPRO}(){$ENDIF} ));
          Name := @NameDispose;
        end;
    end;
    Res^.Concat( New( pAsmInstruction, Create_JSymbol(
      caiCALL, Name^)));

    if CodeTree^.Node.CodeType = cctNEW then
      if Assigned( CodeTree^.Node.CDcode) then
        begin
          OldCounter := Counter;
          Counter := 0;

          Res^.Concat( _POP_( Reg));
          CreateReference( crDefaultSeg, Reg, crNoRegister, 1, 0, nil,
            csDWord, Ref);
          Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
            caiMOV, Reg, Ref)));
          Res^.Concat( _PUSH_( Reg));
          Res^.Concat( New( pAsmInstruction, Create_Ref_Offset(
            caiMOV, Ref,
            pObjectDefinition( CodeTree^.Node.CDcode^.Node.SelfCode^.
              Left^.ResType)^.GetVMTname, 0)));
          if Assigned( CodeTree^.Node.CDcode^.Right) and
            ( CodeTree^.Node.CDcode^.Right^.Node.CodeType = cctFunctionParam) then
            DoFunctionParam( CodeTree^.Node.CDcode^.Right, cctPascal);
          Res^.Concat( New( pAsmInstruction, Create_JSymbol(
            caiCALL, CodeTree^.Node.CDcode^.Left^.Node.FuncSym^.AsmName )));

          if Counter <> 0 then
            DecTempSize( Counter);
          Counter := OldCounter;
        end;

    if CodeTree^.Location.Location = clRegister then
      begin
        if CodeTree^.Node.CodeType = cctNEW then
          begin
            if Assigned( CodeTree^.Left) then
              GetReference( CodeTree, crNoRegister, Ref)
            else
              begin
                CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
                  -LocalSize - CurTempSize, nil, csDefault, Ref);
                DecTempSize( 4);
              end;
            Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
              caiMOV, Reg, Ref)));
          end;
        UsedRegisters := OldUsedRegisters;
        PopUsedRegisters;
        UseRegister( Reg, IsPush);
      end
    else
      begin
        UsedRegisters := OldUsedRegisters;
        PopUsedRegisters;
      end;
  end;


procedure tCodeGenerator.DoAssigned( CodeTree: pCodeTree);
  var
    Reg: tRegister;
    IsPush: Boolean;
  begin
    case CodeTree^.Location.Location of
      {clRegister:
        begin
          CodeTree^.Left^.Location := CodeTree^.Location;
          DoExpression( CodeTree^.Left);
          Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
            caiOR, CodeTree^.Location.Register, CodeTree^.Location.Register)));
          Reg := GetReg( CodeTree^.Location.Register, csByte);
          Res^.Concat( New( pAsmInstruction, Create_Reg(
            caiSETNZ, Reg)));
          Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
            caiMOVZX, CodeTree^.Location.Register, Reg)));
        end;}
      clFlags:
        begin
          Reg := GetRegister( crNoRegister);
          UseRegister( Reg, IsPush);
          CodeTree^.Left^.Location.Location := clRegister;
          CodeTree^.Left^.Location.Register := Reg;
          DoExpression( CodeTree^.Left);
          Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
            caiOR, Reg, Reg)));
          ReleaseRegister( Reg, IsPush);
          if Assigned( CodeTree^.Location.LabelTrue) then
            begin
              Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                caiJNZ, CodeTree^.Location.LabelTrue^)));
              Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                caiJMP, CodeTree^.Location.LabelFalse^)));
            end;
          CodeTree^.Location.ResultFlag := cfNotEqual;
        end;
    end;
  end;


procedure tCodeGenerator.DoConcat( CodeTree: pCodeTree);
  var
    Ref: tReference;
    OldUsedRegisters: tRegisterSet;
    CurCode: pCodeTree;
    OldCounter: LongInt;
  begin
    if CodeTree^.Location.Location = clMemory then
      begin
        OldCounter := Counter;
        PushUsedRegisters;
        OldUsedRegisters := UsedRegisters;
        UsedRegisters := [];
        CodeTree^.Left^.Location := CodeTree^.Location;
        DoExpression( CodeTree^.Left);
        CurCode := CodeTree^.Right;
        while Assigned( CurCode) do
          begin
            Counter := 0;
            Res^.Concat(
              _LEA_( crEAX, CodeTree^.Location.Reference));
            Res^.Concat(
              _PUSH_( crEAX));
            DoPushParam( CurCode^.Right);
            Res^.Concat(
              _PUSH_const( 255));
            Res^.Concat( New( pAsmInstruction, Create_JSymbol(
              caiCALL, NameStrCat)));
            CurCode := CurCode^.Left;
            DecTempSize( Counter);
          end;
        UsedRegisters := OldUsedRegisters;
        PopUsedRegisters;
        Counter := OldCounter;
      end;
  end;


procedure tCodeGenerator.DoIncludeExclude( CodeTree: pCodeTree; FuncName: String);
  var
    Ref: tReference;
    OldUsedRegisters: tRegisterSet;
    IsPush: Boolean;
  begin
    OldUsedRegisters := UsedRegisters;
    PushUsedRegisters;
    UsedRegisters := [];

    UseRegister( crEAX, IsPush);
    GetReference( CodeTree^.Left, crEAX, Ref);
    Res^.Concat(
      _PUSH_( crEAX));
    DoPushParam( CodeTree^.Right);
    Res^.Concat(
      _PUSH_const( pSetDefinition(CodeTree^.Left^.ResType)^.Min ));
    Res^.Concat(
      _PUSH_const( pSetDefinition(CodeTree^.Left^.ResType)^.Max ));
    Res^.Concat( New( pAsmInstruction, Create_JSymbol(
      caiCALL, FuncName)));

    UsedRegisters := OldUsedRegisters;
    PopUsedRegisters;
  end;


procedure tCodeGenerator.DoFunction( CodeTree: pCodeTree);
  begin
    if CodeTree^.Location.Location = clRegister then
      begin
        Res^.Concat( New( pAsmInstruction, Create_Reg_Offset(
          caiMOV, CodeTree^.Location.Register,
          CodeTree^.Node.FuncSym^.AsmName, 0 )));
      end;
  end;


procedure tCodeGenerator.DoMem( CodeTree: pCodeTree);
  var
    Ref: tReference;
    Size: tSize;
    AO: tAsmOp;
  begin
    if (CodeTree^.Location.Location = clRegister) and
      (CodeTree^.ResType^.DefType = cOrdDefinition) then
      begin
        CodeTree^.Left^.Location := CodeTree^.Location;
        DoExpression( CodeTree^.Left);
        Size := GetSize( CodeTree^.ResType^.GetSize);
        CreateReference( crDefaultSeg, CodeTree^.Location.Register, crNoRegister, 1, 0,
          nil, Size, Ref);
        case CodeTree^.ResType^.DefType of
          cOrdDefinition,
          cUserOrdDefinition,
          cBooleanDefinition,
          cPointerDefinition:
            begin
              if Size = csDWord then
                AO := caiMOV
              else
                AO := caiMOVZX;
              Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
                AO, CodeTree^.Location.Register, Ref)));
            end;
          cRealDefinition:
            Res^.Concat( New( pAsmInstruction, Create_Ref(
              caiFLD, Ref)));
        end;
      end;
  end;

procedure tCodeGenerator.DoPort( CodeTree: pCodeTree);
  var
    IsPushEAX, IsPushEDX: Boolean;
    Reg: tRegister;
    Size: tSize;
    AO: tAsmOP;
  begin
    if (CodeTree^.Location.Location = clRegister) and
      ( CodeTree^.ResType^.DefType = cOrdDefinition) then
      begin
        CodeTree^.Left^.Location := CodeTree^.Location;
        DoExpression( CodeTree^.Left);
        Size := GetSize( CodeTree^.ResType^.GetSize);
        Reg := CodeTree^.Location.Register;
        if Reg <> crEAX then
          UseRegister( crEAX, IsPushEAX);
        if Reg <> crEDX then
          begin
            UseRegister( crEDX, IsPushEDX);
            Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
              caiMOV, crEDX, Reg)));
          end;
        Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
          caiIN, GetReg( crEAX, Size), crDX)));
        if Reg <> crEDX then
          ReleaseRegister( crEDX, IsPushEDX);
        if Reg <> crEAX then
          begin
            if Size <> csDWord then
              AO := caiMOVZX
            else
              AO := caiMOV;
            Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
              AO, Reg, GetReg( crEAX, Size) )));
          end
        else if Size <> csDWord then
          Res^.Concat( New( pAsmInstruction, Create_Reg_Reg(
            caiMOVZX, crEAX, GetReg( crEAX, Size) )));
      end;
  end;


procedure tCodeGenerator.DoTypeOfExpression( CodeTree: pCodeTree);
  var
    Ref: tReference;
  begin
    if CodeTree^.Location.Location = clRegister then
      begin
        GetReference( CodeTree^.Left, CodeTree^.Location.Register, Ref);
        Ref.Size := csDWord;
        Res^.Concat( New( pAsmInstruction, Create_Reg_Ref(
          caiMov, CodeTree^.Location.Register, Ref)));
      end;
  end;

procedure tCodeGenerator.DoTypeOfType( CodeTree: pCodeTree);
  begin
    if CodeTree^.Location.Location = clRegister then
      begin
        Res^.Concat( New( pAsmInstruction, Create_Reg_Offset(
          caiMOV, CodeTree^.Location.Register,
          CodeTree^.Node.ObjectDef^.GetVMTname, 0)));
      end;
  end;


procedure tCodeGenerator.DoIfExpression( CodeTree: pCodeTree);
  var
    ThenLab, ElseLab, EndLab: String;
    IsPush: Boolean;
    P: pAsmCode;
  begin
    ThenLab := CurCompiler^.CreateLabel;
    ElseLab := CurCompiler^.CreateLabel;
    EndLab := CurCompiler^.CreateLabel;
    CodeTree^.Right^.Location.Location := clFlags;
    CodeTree^.Right^.Location.LabelTrue := NewStr( ThenLab);
    CodeTree^.Right^.Location.LabelFalse := NewStr( ElseLab);
    DoExpression( CodeTree^.Right);
    P := Res^.Last;

    Res^.Concat( MakeLabel( New( pAsmInstruction, Create( caiNoInstruction)),
      ThenLab));
    CodeTree^.Node.IFBlock^.Location := CodeTree^.Location;
    DoExpression( CodeTree^.Node.IFBlock);
    Res^.Concat( New( pAsmInstruction, Create_JSymbol( caiJMP, EndLab)));

    Res^.Concat( MakeLabel( New( pAsmInstruction, Create( caiNoInstruction)),
      ELSELab));
    CodeTree^.Node.ElseBlock^.Location := CodeTree^.Location;
    DoExpression( CodeTree^.Node.ELSEBlock);
    Res^.Concat( MakeLabel( New( pAsmInstruction, Create( caiNoInstruction)),
      EndLab));
  end;


procedure tCodeGenerator.DoAsmBlock( CodeTree: pCodeTree);

  procedure DoOperand( var Operand: tOperand);
    begin
      case Operand.Location of
        clSymbol,
        clOffset:
          if Assigned( Operand.Symbol) then
            begin
              DisposeStr( Operand.LabelName);
              Operand.LabelName := NewStr( pSymbol( Operand.Symbol)^.AsmName{$IFDEF PPRO}(){$ENDIF});
            end;
      end;
    end;

  var
    AsmCode: pAsmCode;
    AsmProc : pProcAsm;
  begin
    AsmProc := CodeTree^.Node.Block;
    while Assigned( AsmProc^.First) do
      begin
        AsmCode := AsmProc^.First;
        DoOperand( AsmCode^.Instruction^.Op1);
        DoOperand( AsmCode^.Instruction^.Op2);
        DoOperand( AsmCode^.Instruction^.Op3);
        Res^.Concat( AsmCode^.Instruction);
        AsmProc^.First := AsmCode^.Next;
        Dispose( AsmCode);
      end;
    AsmProc^.Last := nil;
  end;


function tCodeGenerator.GetRegister( LockedReg: tRegister): tRegister;
  var
    Reg: tRegister;
  begin
    for Reg := crEAX to crEBX do
      begin
        if not (Reg in UsedRegisters) then
          begin
            GetRegister := Reg;
            Exit;
          end;
      end;
    for Reg := crEAX to crEBX do
      if Reg <> LockedReg then
        begin
          GetRegister := Reg;
          Exit;
        end;
    GetRegister := crNoRegister;
  end;

procedure tCodeGenerator.UseRegister( Reg: tRegister; var IsPush: Boolean);
  begin
    if Reg <> crNoRegister then
      begin
        if Reg in UsedRegisters then
          begin
            Res^.Concat(
              _PUSH_( Reg));
            IsPush := True;
            UsedRegisters := UsedRegisters - [Reg];
          end
        else
          begin
            IsPush := False;
            {UsedRegisters := UsedRegisters + [Reg];}
          end;
      end;
  end;

procedure tCodeGenerator.ReleaseRegister( Reg: tRegister; IsPush: Boolean);
  begin
    if Reg <> crNoRegister then
      begin
        if IsPush then
          begin
            Res^.Concat( _POP_( Reg) );
            UsedRegisters := UsedRegisters + [Reg];
          end;
{        else
          UsedRegisters := UsedRegisters - [Reg];}
      end;
  end;

procedure tCodeGenerator.LockRegister( Reg: tRegister);
  begin
    UsedRegisters := UsedRegisters + [Reg];
  end;

procedure tCodeGenerator.UnlockRegister( Reg: tRegister);
  begin
    UsedRegisters := UsedRegisters - [Reg];
  end;

procedure tCodeGenerator.PushUsedRegisters;
  var
    Reg: tRegister;
  begin
    for Reg := crEAX to crEBX do
      if Reg in UsedRegisters then
        Res^.Concat(
          _PUSH_( Reg));
  end;

procedure tCodeGenerator.PopUsedRegisters;
  var
    Reg: tRegister;
  begin
    for Reg := crEBX downto crEAX do
      if Reg in UsedRegisters then
        Res^.Concat(
          _POP_( Reg));
  end;

procedure tCodeGenerator.DoIfBlock( CodeTree: pCodeTree);
  var
    ThenLab, ElseLab, EndLab: String;
    IsPush: Boolean;
    P: pAsmCode;
  begin
    ThenLab := CurCompiler^.CreateLabel;
    ElseLab := CurCompiler^.CreateLabel;
    EndLab := CurCompiler^.CreateLabel;
    UsedRegisters := [];
    CodeTree^.Right^.Location.Location := clFlags;
    CodeTree^.Right^.Location.LabelTrue := NewStr( ThenLab);
    CodeTree^.Right^.Location.LabelFalse := NewStr( ElseLab);
    GenerateExpression( CodeTree^.Right);
    P := Res^.Last;

    Res^.Concat( MakeLabel( New( pAsmInstruction, Create( caiNoInstruction)),
      ThenLab));
    OptomizeAsm( P, Res^.Last);
    GenerateAsm( CodeTree^.Node.IFBlock);
    Res^.Concat( New( pAsmInstruction, Create_JSymbol( caiJMP, EndLab)));

    Res^.Concat( MakeLabel( New( pAsmInstruction, Create( caiNoInstruction)),
      ELSELab));
    GenerateAsm( CodeTree^.Node.ELSEBlock);
    Res^.Concat( MakeLabel( New( pAsmInstruction, Create( caiNoInstruction)),
      EndLab));
  end;

procedure tCodeGenerator.DoWhileBlock( CodeTree: pCodeTree);
  var
    BegLab, LoopLab, EndLab: String;
    IsPush: Boolean;
  begin
    BegLab := CurCompiler^.CreateLabel;
    LoopLab := CurCompiler^.CreateLabel;
    EndLab := CurCompiler^.CreateLabel;

    Res^.Concat( MakeLabel( New( pAsmInstruction, Create(
      caiNoInstruction)), BegLab));
    UsedRegisters := [];
    CodeTree^.Right^.Location.Location := clFlags;
    CodeTree^.Right^.Location.LabelTrue := NewStr( LoopLab);
    CodeTree^.Right^.Location.LabelFalse := NewStr( EndLab);
    GenerateExpression( CodeTree^.Right);

    PushLoop( EndLab, BegLab);
    Res^.Concat( MakeLabel( New( pAsmInstruction, Create(
      caiNoInstruction)), LoopLab));
    if Assigned( CodeTree^.Node.LoopBlock) then
      GenerateAsm( CodeTree^.Node.LoopBlock);
    PopLoop;
    Res^.Concat( New( pAsmInstruction, Create_JSymbol( caiJMP,
      BegLab)));

    Res^.Concat( MakeLabel( New( pAsmInstruction, Create(
      caiNoInstruction)), EndLab));
  end;

procedure tCodeGenerator.DoRepeatUntilBlock( CodeTree: pCodeTree);
  var
    BegLab, EndLab, CondLab: String;
    CurCode: pCodeTree;
    IsPush: Boolean;
  begin
    BegLab := CurCompiler^.CreateLabel;
    EndLab := CurCompiler^.CreateLabel;
    CondLab := CurCompiler^.CreateLabel;
    Res^.Concat( MakeLabel( New( pAsmInstruction, Create(
      caiNoInstruction)), BegLab));
    CurCode := CodeTree^.Node.LoopBlock;
    PushLoop( EndLab, CondLab);
    while Assigned( CurCode) do
      begin
        GenerateAsm( CurCode);
        CurCode := CurCode^.Left;
      end;
    PopLoop;

    Res^.Concat( MakeLabel( New( pAsmInstruction, Create(
      caiNoInstruction)), CondLab));
    UsedRegisters := [];
    {UseRegister( crEAX, IsPush);
    CodeTree^.Right^.Location.Location := clRegister;
    CodeTree^.Right^.Location.Register := crEAX;}
    CodeTree^.Right^.Location.Location := clFlags;
    CodeTree^.Right^.Location.LabelTrue := NewStr( EndLab);
    CodeTree^.Right^.Location.LabelFalse := NewStr( BegLab);
    GenerateExpression( CodeTree^.Right);
    {ReleaseRegister( crEAX, IsPush);
    Res^.Concat( New( pAsmInstruction, Create_Reg_Reg( caiOR,
      crAL, crAL)));
    Res^.Concat( New( pAsmInstruction, Create_JSymbol( caiJZ,
      BegLab)));}

    Res^.Concat( MakeLabel( New( pAsmInstruction, Create(
      caiNoInstruction)), EndLab));
  end;

procedure tCodeGenerator.DoFORBlock( CodeTree: pCodeTree);
  var
    BegLab, IncLab, EndLab: String;
    Ref1, Ref2: tReference;
    IsPush: Boolean;
    AO: tAsmOp;
  begin
    BegLab := CurCompiler^.CreateLabel;
    IncLab := CurCompiler^.CreateLabel;
    EndLab := CurCompiler^.CreateLabel;
    UsedRegisters := [];
    UseRegister( crEAX, IsPush);
    CodeTree^.Node.Min^.Location.Location := clRegister;
    CodeTree^.Node.Min^.Location.Register := crEAX;
    GenerateExpression( CodeTree^.Node.Min);
    UseRegister( crEBX, IsPush);
    GetReference( CodeTree^.Node.Counter, crEBX, Ref1);
    Res^.Concat( New( pAsmInstruction, Create_Ref_Reg( caiMOV,
      Ref1, GetEAX( Ref1.Size))));
    ReleaseRegister( crEBX, False);

    CodeTree^.Node.Max^.Location.Location := clRegister;
    CodeTree^.Node.Max^.Location.Register := crEAX;
    GenerateExpression( CodeTree^.Node.Max);
    IncTempSize( 4);
    Counter := 0;
    CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
      -(CurTempSize + LocalSize), nil,
      GetSize( CodeTree^.Node.Counter^.ResType^.GetSize), Ref2);
    Res^.Concat( New( pAsmInstruction, Create_Ref_Reg( caiMOV,
      Ref2, GetEAX( Ref2.Size))));

    UseRegister( crEBX, IsPush);
    GetReference( CodeTree^.Node.Counter, crEAX, Ref1);
    Res^.Concat( New( pAsmInstruction, Create_Reg_Ref( caiMOV,
      GetEAX( Ref1.Size), Ref1)));
    ReleaseRegister( crEBX, False);
    Res^.Concat( New( pAsmInstruction, Create_Reg_Ref( caiCMP,
      GetEAX( Ref2.Size), Ref2)));
    if CodeTree^.Node.IsForward then
      if IsSigned( CodeTree^.Node.Counter^.ResType) then
        AO := caiJG
      else
        AO := caiJA
    else
      if IsSigned( CodeTree^.Node.Counter^.ResType) then
        AO := caiJL
      else
        AO := caiJB;

    Res^.Concat( New( pAsmInstruction, Create_JSymbol( AO,
        EndLab)));

    Res^.Concat( MakeLabel( New( pAsmInstruction, Create(
      caiNoInstruction)), BegLab));

    PushLoop( EndLab, IncLab);
    UsedRegisters := [];
    if Assigned( CodeTree^.Right) then
      GenerateAsm( CodeTree^.Right);
    PopLoop;

    Res^.Concat( MakeLabel( New( pAsmInstruction, Create(
      caiNoInstruction)), IncLab));
    UseRegister( crEAX, IsPush);
    GetReference( CodeTree^.Node.Counter, crEAX, Ref1);
    Res^.Concat( New( pAsmInstruction, Create_Reg_Ref( caiMOV,
      GetEBX( Ref1.Size), Ref1)));
    Res^.Concat( New( pAsmInstruction, Create_Reg_Ref( caiCMP,
      GetEBX( Ref2.Size), Ref2)));
    Res^.Concat( New( pAsmInstruction, Create_JSymbol(
      caiJZ, EndLab)));
    if CodeTree^.Node.IsForward then
      Res^.Concat( New( pAsmInstruction, Create_Ref( caiInc, Ref1)))
    else
      Res^.Concat( New( pAsmInstruction, Create_Ref( caiDec, Ref1)));
    Res^.Concat( New( pAsmInstruction, Create_JSymbol( caiJMP,
      BegLab)));

    Res^.Concat( MakeLabel( New( pAsmInstruction, Create(
      caiNoInstruction)), EndLab));
    DecTempSize( 4);
    UsedRegisters := [];
  end;


procedure tCodeGenerator.DoCASEBlock( CodeTree: pCodeTree);
  var
    CurCode: pCodeTree;
    NextLab, EndLab: String;
    Reg: tRegister;
    IsPush: Boolean;

  procedure DoCaseCondition( CaseCond: pCodeTree);
    var
      CurCode: pCodeTree;
      TrueLab: String;
    begin
      CurCode := CaseCond;
      TrueLab := CurCompiler^.CreateLabel;
      while Assigned( CurCode) do
        begin
          case CurCode^.Node.CodeType of
            cctCaseEqual:
              begin
                Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                  caiCMP, Reg, CurCode^.Node.Value)));
                Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                  caiJZ, TrueLab)));
              end;
            cctCaseBetween:
              begin
                Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                  caiSUB, Reg, CurCode^.Node.MinValue)));
                Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                  caiCMP, Reg, CurCode^.Node.MaxValue - CurCode^.Node.MinValue)));
                Res^.Concat( New( pAsmInstruction, Create_JSymbol(
                  caiJBE, TrueLab)));
                Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
                  caiADD, Reg, CurCode^.Node.MinValue)));
              end;
          end;
          CurCode := CurCode^.Left;
        end;
      Res^.Concat( New( pAsmInstruction, Create_JSymbol(
        caiJMP, NextLab)));
      Res^.Concat( MakeLabel( New( pAsmInstruction, Create(
        caiNoInstruction)), TrueLab));
    end;

  begin
    UsedRegisters := [];
    Reg := crEAX;
    UseRegister( Reg, IsPush);
    CodeTree^.Node.Expression^.Location.Location := clRegister;
    CodeTree^.Node.Expression^.Location.Register := Reg;
    GenerateExpression( CodeTree^.Node.Expression);
    ReleaseRegister( Reg, IsPush);
    CurCode := CodeTree^.Right;
    EndLab := CurCompiler^.CreateLabel;
    NextLab := CurCompiler^.CreateLabel;
    while Assigned( CurCode) do
      begin
        DoCaseCondition( CurCode^.Right);
        GenerateAsm( CurCode^.Node.Statement);
        CurCode := CurCode^.Left;
        Res^.Concat( New( pAsmInstruction, Create_JSymbol(
          caiJMP, EndLab)));
        Res^.Concat( MakeLabel( New( pAsmInstruction, Create(
          caiNoInstruction)), NextLab));
        NextLab := CurCompiler^.CreateLabel;
      end;

    if Assigned( CodeTree^.Node.ElseStatement) then
      GenerateAsm( CodeTree^.Node.ElseStatement);

    Res^.Concat( MakeLabel( New( pAsmInstruction, Create(
      caiNoInstruction)), EndLab));
  end;


procedure tCodeGenerator.DoBreak;
  begin
    if Assigned( LoopStack) and Assigned( LoopStack^.EndLabel) then
      begin
        Res^.Concat( New( pAsmInstruction, Create_JSymbol(
          caiJMP, LoopStack^.EndLabel^)));
      end
    else
      CurCompiler^.Error( erInternalError, CurCompiler^.Files^.PrevLine,
        CurCompiler^.Files^.PrevCol, '');
  end;

procedure tCodeGenerator.DoContinue;
  begin
    if Assigned( LoopStack) and Assigned( LoopStack^.ConditionLabel) then
      begin
        Res^.Concat( New( pAsmInstruction, Create_JSymbol(
          caiJMP, LoopStack^.ConditionLabel^)));
      end
    else
      CurCompiler^.Error( erInternalError, CurCompiler^.Files^.PrevLine,
        CurCompiler^.Files^.PrevCol, '');
  end;

procedure tCodeGenerator.DoEXIT;
  begin
    if Assigned( ExitLabel) then
      Res^.Concat( New( pAsmInstruction, Create_JSymbol(
        caiJMP, ExitLabel^)))
    else
      CurCompiler^.Error( erInternalError, CurCompiler^.Files^.PrevLine,
        CurCompiler^.Files^.PrevCol, '');
  end;


procedure tCodeGenerator.DoRealConst( CodeTree: pCodeTree);
  var
    TypeDef: pDefinition;
    Sym: pTypedConstSymbol;
    SymName: String[20];
    Ref: tReference;
  begin
    if CodeTree^.Node.RealValue = 1.0 then
      Res^.Concat( New( pAsmInstruction, Create(
        caiFLD1)))
    else if CodeTree^.Node.RealValue = PI then
      Res^.Concat( New( pAsmInstruction, Create(
        caiFLDPI)))
    else if CodeTree^.Node.RealValue = 0.0 then
      Res^.Concat( New( pAsmInstruction, Create(
        caiFLDZ)))
    else
      begin
        TypeDef := CurCompiler^.ExtendedDef;{CodeTree^.ResType;}
        SymName := CurCompiler^.CreateLabel;
        Sym := New( pTypedConstSymbol, Init( SymName, TypeDef, 0));
        Sym^.Value.RealValue := CodeTree^.Node.RealValue;
        Sym^.Value.ValueType := cvRealValue;
        CurCompiler^.GlobalSymbols^.Insert( Sym);
        CreateReference( crDefaultSeg, crNoRegister, crNoRegister, 1, 0,
          NewStr(Sym^.AsmName), csTByte, Ref);
        Res^.Concat( New( pAsmInstruction, Create_Ref(
          caiFLD, Ref)));
      end;
  end;


procedure tCodeGenerator.DoLoadIntConstToFpuStack( CodeTree: pCodeTree);
  var
    TypeDef: pDefinition;
    Sym: pTypedConstSymbol;
    SymName: String[20];
    Ref: tReference;
  begin
    TypeDef := CodeTree^.ResType;
    SymName := CurCompiler^.CreateLabel;
    Sym := New( pTypedConstSymbol, Init( SymName, TypeDef, 0));
    Sym^.Value.IntValue := CodeTree^.Node.IntValue;
    Sym^.Value.ValueType := cvOrdinalValue;
    CurCompiler^.GlobalSymbols^.Insert( Sym);
    CreateReference( crDefaultSeg, crNoRegister, crNoRegister, 1, 0,
      NewStr(Sym^.AsmName), csDWord, Ref);
    Res^.Concat( New( pAsmInstruction, Create_Ref(
      caiFILD, Ref)));
  end;


procedure tCodeGenerator.PushLoop( const EndLab, ConditionLab: String);
  var
    P: pLoopStack;
  begin
    New( P);
    P^.EndLabel := NewStr( EndLab);
    P^.ConditionLabel := NewStr( ConditionLab);
    P^.Next := LoopStack;
    LoopStack := P;
  end;

procedure tCodeGenerator.PopLoop;
  var
    P: pLoopStack;
  begin
    P := LoopStack;
    if Assigned( P) then
      begin
        LoopStack := P^.Next;
        DisposeStr( P^.EndLabel);
        DisposeStr( P^.ConditionLabel);
        Dispose( P);
      end;
  end;


procedure tCodeGenerator.GenerateAsm( CodeTree: pCodeTree);
  begin
    if not Assigned( CodeTree) then Exit;
    case CodeTree^.Node.CodeType of
      cctExpression:
        begin
          UsedRegisters := [];
          GenerateExpression( CodeTree^.Right);
        end;
      cctBlock:
        DoBlock( CodeTree);
      cctAsmBlock:
        DoAsmBlock( CodeTree);
      cctIFBlock:
        DoIFBlock( CodeTree);
      cctWHILEBlock:
        DoWhileBlock( CodeTree);
      cctRepeatUntil:
        DoRepeatUntilBlock( CodeTree);
      cctFORBlock:
        DoFORBlock( CodeTree);
      cctCASEBlock:
        DoCASEBlock( CodeTree);
      cctWITHBlock:
        DoWithBlock( CodeTree);
      cctBREAK:
        DoBreak;
      cctContinue:
        DoContinue;
      cctEXIT:
        DoEXIT;
      cctLabel:
        DoLabel( CodeTree);
      cctGOTO:
        DoGOTO( CodeTree);
    end;
    {if Assigned( Res^.Last) and Assigned( Res^.Last^.Instruction) then
      Res^.Last^.Instruction^.Comment := NewStr( '; ' + ToStr( CodeTree^.Line) + _EOL_);}
  end;


procedure tCodeGenerator.DoWITHblock( CodeTree: pCodeTree);
  var
    Ref: tReference;
    IsPush: Boolean;
  begin
    UseRegister( crEAX, IsPush);
    CodeTree^.Right^.Location.Location := clRegister;
    CodeTree^.Right^.Location.Register := crEAX;
    GenerateExpression( CodeTree^.Right);
    ReleaseRegister( crEAX, IsPush);
    IncTempSize( 4);
    Counter := 0;
    CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
      -LocalSize-CurTempSize, nil, csDWord, Ref);
    Res^.Concat( New( pAsmInstruction, Create_Ref_Reg(
      caiMOV, Ref, crEAX)));
    GenerateAsm( CodeTree^.Node.WithBlock);
    DecTempSize( 4);
  end;


procedure tCodeGenerator.DoLabel( CodeTree: pCodeTree);
  begin
    Res^.Concat( MakeLabel( New( pAsmInstruction, Create( caiNoInstruction)),
      CodeTree^.Node.LabelSymbol^.AsmName));
  end;


procedure tCodeGenerator.DoGOTO( CodeTree: pCodeTree);
  begin
    Res^.Concat( New( pAsmInstruction, Create_JSymbol(
      caiJMP, CodeTree^.Node.LabelSymbol^.AsmName)));
  end;


procedure tCodeGenerator.IncTempSize( L: LongInt);
  begin
    Inc( CurTempSize, L);
    Inc( Counter, L);
  end;

procedure tCodeGenerator.DecTempSize( L: LongInt);
  begin
    if CurTempSize > Res^.TempSize then
      Res^.TempSize := CurTempSize;
    Dec( CurTempSize, L);
    Counter := 0;
  end;


procedure tCodeGenerator.CopyMemory( Count: LongInt);
  var
    AI: pAsmInstruction;
    IsPush: Boolean;
  begin
    IsPush := False;
    if crECX in UsedRegisters then
      begin
        IsPush := True;
        Res^.Concat(
          _PUSH_( crECX));
      end;

    Res^.Concat( New( pAsmInstruction, Create_Reg_Const(
      caiMOV, crECX, Count)));

    Res^.Concat( New( pAsmInstruction, Create( caiCLD)));
    AI := New( pAsmInstruction, Create( caiMOVSB));
    AI^.Prefix := caiREP;
    Res^.Concat( AI);
    if IsPush then
      Res^.Concat(
        _POP_( crECX));
  end;


procedure tCodeGenerator.CopyObject( VMT: String);
  begin
    PushUsedRegisters;
    Res^.Concat( _PUSH_( crESI));
    Res^.Concat( New( pAsmInstruction, Create_Reg_Offset(
      caiMOV, crESI, VMT, 0 )));
    Res^.Concat( _PUSH_( crESI));
    Res^.Concat( _PUSH_( crEDI));
    Res^.Concat( New( pAsmInstruction, Create_JSymbol(
      caiCALL, NameCopyObject)));
    PopUsedRegisters;
  end;

procedure tCodeGenerator.GenerateExpression( CodeTree: pCodeTree);
  var
    First: pAsmCode;
  begin
    Res^.Concat( New( pComment, Create(
      ' Line: ' + ToStr( CodeTree^.Line) + ' ; Column: ' + ToStr( CodeTree^.Col) ) ));
    First := Res^.Last;
    DoExpression( CodeTree);
    Res^.Concat( New( pComment, Create(
      ' Line: ' + ToStr( CodeTree^.Line) + ' ; Column: ' + ToStr( CodeTree^.Col) ) ));
    OptomizeAsm( First, Res^.Last);
  end;

end.