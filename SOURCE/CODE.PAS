{                    GNU GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Full text of license:
 https://www.gnu.org/licenses/gpl-3.0.en.html

 (c) Copyright 2022 DosWord
 (c) Copyright 1997-1998 Iggor Khachko - hachko@icl.kazan.su }

{
  Дата создания: 27.09.97
}

{$IFDEF TP}
{$X+,V-,G+,N+,E-,B-,T-}
{$IFDEF DEBUG}
{$I+,S+,R+,C+}
{$ELSE}
{$I-,S-,R-,C-}
{$ENDIF}
{$ENDIF}

unit Code;

interface

uses Objects, Symbols, IAsm386;

const
  cdtNormal             = 0;
  cdtDisposeResult      = 1;

type

  tCodeType = (
    cctFunctionCall, cctLoadValue, cctAssignment, cctOrdConst, cctRealConst,
    cctIntConst, cctCharConst, cctStringConst, cctBoolConst, cctPCharConst,
    cctAddition, cctSubtraction, cctMultiplication, cctDivision, cctDiv,
    cctMod, cctAnd, cctShr, cctShl, cctOr, cctXor, cctNot, cctNeg,
    cctEqual, cctUnequal, cctGreater, cctLess, cctGreaterEq, cctLessEq,
    cctExpression, cctBlock, cctTypeConversion, cctVariable, cctDeref,
    cctFunctionParam, cctLoadAddress, cctFuncRet, cctAsmBlock,
    cctIFBlock, cctWhileBlock, cctRepeatUntil, cctForBlock,
    cctCaseBlock, cctBreak, cctContinue, cctPlusAsn, cctMinusAsn,
    cctAndAsn, cctOrAsn, cctStarAsn, cctSlashAsn, cctDivAsn, cctModAsn,
    cctShlAsn, cctShrAsn, cctXorAsn, cctPred, cctSucc, cctInc, cctDec,
    cctFunction, cctCaseNode, cctCaseEqual, cctCaseBetween, cctEXIT,
    cctSetConst, cctSetRange, cctSetItem, cctIN, cctLength, cctAssign,
    cctWrite, cctWriteLn, cctRead, cctReadLn, cctWriteParam,
    cctArithmeticFunction, cctPointerConst, cctNew, cctDispose,
    cctAssigned, cctConcat, cctInclude, cctExclude, cctLow, cctHigh,
    cctWITHBlock, cctWithSymbol, cctPort, cctMem, cctTypeOfExpression,
    cctTypeOfType, cctLabel, cctGOTO
  );

  tTypes = (
    _8bit, _16bit, _32bit, _real
  );

  tTypeConversion = (
    ccNoConversion, cc8bit_2_16bit, cc8bit_2_32bit, cc8bit_2_Real,
    cc16bit_2_8bit,                 cc16bit_2_32bit, cc16bit_2_Real,
    cc32bit_2_8bit, cc32bit_2_16bit,                  cc32bit_2_Real,
    ccReal_2_8bit, ccReal_2_16bit, ccReal_2_32bit,
    ccChar_2_String, ccUserConversion
  );

  pCodeTree = ^tCodeTree;
  pCodeRec = ^tCodeRec;
  tCodeRec = record
    case CodeType:tCodeType of
      cctFunction:(
        FuncSym: pFunctionSymbol;
      );
      cctVariable:(
        Symbol: pVariableSymbol;
      );
      cctOrdConst:(
        OrdValue: LongInt;
      );
      cctIntConst:(
        IntValue: LongInt;
      );
      cctCharConst:(
        CharValue: Char;
      );
      cctRealConst:(
        RealValue: Extended;
      );
      cctStringConst:(
        StringValue: pString;
      );
      cctBoolConst:(
        BoolValue: Boolean;
      );
      cctSetConst:(
        SetValue: pByteSet;
      );
      cctPointerConst:(
        PointerValue: LongInt;
        PointerSymbol: pSymbol;
        PointerName: pString;
      );
      cctTypeConversion:(
        Conversion: tTypeConversion;
      );
      cctAsmBlock:
      (
        Block: Pointer;
      );
      cctIFBlock:
      (
        IFBlock, ELSEBlock: pCodeTree;
      );
      cctWhileBlock,
      cctRepeatUntil:(
        LoopBlock: pCodeTree;
      );
      cctWITHBlock:(
        WithBlock: pCodeTree;
      );
      cctForBlock:(
        Counter: pCodeTree;
        Min, Max: pCodeTree;
        IsForward: Boolean;
      );
      cctCaseBlock:(
        Expression, ELSEStatement: pCodeTree;
      );
      cctCaseNode:(
        Statement: pCodeTree;
      );
      cctCaseEqual:(
        Value: LongInt;
      );
      cctCaseBetween:(
        MinValue, MaxValue: LongInt;
      );
      cctWriteParam:(
        Len: pCodeTree;
        Digs: pCodeTree;
      );
      cctArithmeticFunction:(
        SysSymbolType: tSystemSymbolType;
      );
      cctFunctionCall:(
        SelfCode: pCodeTree;
        InheritedCall: Boolean;
        CallType: tCallType;
      );
      cctNew, cctDispose:(
        CDcode: pCodeTree;
      );
      cctTypeOfType:(
        ObjectDef: pObjectDefinition;
      );
      cctLabel,
      cctGOTO:(
        LabelSymbol: pLabelSymbol;
      );
  end;

  tCodeTree = object(tObject)
    Left: pCodeTree;
    Right: pCodeTree;
    ResType: pDefinition;
    DisposeType: LongInt;
    LineNumber: LongInt;
    Node: tCodeRec;
    Line, Col: LongInt;
    Location: tOperand;
    constructor CreateFunctionCall( aFuncTree, aRight, aSelfCode: pCodeTree;
      aLine, aCol: LongInt);
    constructor CreateOrdConst( Value: LongInt; Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateIntConst( Value: LongInt; Result: pDefinition; aLine, aCol: LongInt);
    constructor CreatePointerConst( Value: LongInt; aSymbol: pSymbol; aName: pString;
      Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateCharConst( Value: Char; Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateRealConst( Value: Extended; Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateStringConst( const Value: String; Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateBoolConst( Value: Boolean; Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateSetConst( Value: tByteSet; Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateAddition( aLeft, aRight: pCodeTree; Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateSubtraction( aLeft, aRight: pCodeTree; Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateMultiplication( aLeft, aRight: pCodeTree; Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateDivision( aLeft, aRight: pCodeTree; Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateDiv( aLeft, aRight: pCodeTree; Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateMod( aLeft, aRight: pCodeTree; Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateNeg( Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateNot( Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateAnd( Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateShl( Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateShr( Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateOr( Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateXor( Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateEqual( Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateUnequal( Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateGreater( Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateLess( Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateGreaterEq( Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateLessEq( Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateIN( Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateAssignment( AsnType: tCodeType; Result: pDefinition; aLeft, aRight: pCodeTree; aLine, aCol: LongInt);
    constructor CreateExpression( Expr: pCodeTree; Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateBlock( aBlock: pCodeTree; aLine, aCol: LongInt);
    constructor CreateVariable( aVar: pVariableSymbol; aLine, aCol: LongInt);
    constructor CreateFunction( aFunc: pFunctionSymbol; Result: pDefinition);
    constructor CreateTypeConversion( aConv: tTypeConversion; Result: pDefinition);
    constructor CreateLoadValue( aCodeTree: pCodeTree; Offset: pCodeTree; Result: pDefinition);
    constructor CreateDeref( aLeft: pCodeTree; Result: pDefinition; aLine, aCol: LongInt);
    constructor CreateFuncParam( aLeft, aRight: pCodeTree);
    constructor CreateLoadAddress( CodeTree: pCodeTree; Result: pDefinition);
    constructor CreateFuncRet( Result: pDefinition);
    constructor CreateAsmBlock( AsmBlock: Pointer);
    constructor CreateIFBlock( aCondition, aIF, aELSE: pCodeTree);
    constructor CreateWhileBlock( aCondition, aLoopBlock: pCodeTree);
    constructor CreateRepeatUntilBlock( aCondition, aLoopBlock: pCodeTree);
    constructor CreateFORBlock( aCounter, aMin, aMax, aLoop: pCodeTree;
      aForward: Boolean);
    constructor CreatePred( Expression: pCodeTree);
    constructor CreateSucc( Expression: pCodeTree);
    constructor CreateInc( Variable, Increment: pCodeTree; Result: pDefinition);
    constructor CreateDec( Variable, Decrement: pCodeTree; Result: pDefinition);

    constructor CreateLength( Expression: pCodeTree; Result: pDefinition);

    constructor CreateAssign( aFile, aFileName: pCodeTree);

    constructor CreateArithmetic( aSysSymbol: tSystemSymboltype;
      Expression: pCodeTree; Result: pDefinition);

    constructor CreateNewDispose( CodeType: tCodeType;
      Expression: pCodeTree; Result: pDefinition; aCDcode: pCodeTree);

    constructor CreateAssigned( Expression: pCodeTree; Result: pDefinition);

    constructor CreateConcat( Dest, Source: pCodeTree; Result: pDefinition);

    constructor CreateIncludeExclude( CodeType: tCodeType; Dest, Item: pCodeTree);

    constructor CreateMemPort( aCodeType: tCodeType; aLeft: pCodeTree; aResult: pDefinition);

    constructor CreateWrite( aFileCode, aParams: pCodeTree);
    constructor CreateWriteLn( aFileCode, aParams: pCodeTree);
    constructor CreateRead( aFileCode, aParams: pCodeTree);
    constructor CreateReadLn( aFileCode, aParams: pCodeTree);
    constructor CreateWriteParam( aExpression: pCodeTree; aLen, aDigs: pCodeTree);

    constructor CreateTypeOfExpression( anExpression: pCodeTree; aResType: pDefinition);
    constructor CreateTypeOfType( anObjectDef: pObjectDefinition; aResType: pDefinition);

    constructor CreateCASEBlock( aExpression, aBlock, aElseBlock: pCodeTree);
    constructor CreateCASENode( aCondition, aStatement, aLeft: pCodeTree);
    constructor CreateCaseEqual( aValue: LongInt; aLeft: pCodeTree);
    constructor CreateCaseBetween( aMin, aMax: LongInt; aLeft: pCodeTree);

    constructor CreateBREAK;
    constructor CreateCONTINUE;
    constructor CreateEXIT;

    constructor CreateWITHBlock( anExpression, aBlock: pCodeTree);
    constructor CreateWithSymbol( aLevel: LongInt; Offset: pCodeTree;
      aResult: pDefinition);

    constructor CreateSetItem( aItem: pCodeTree; Result: pDefinition);
    constructor CreateSetRange( aMin, aMax: pCodeTree; Result: pDefinition);

    constructor CreateLabel( aLabel: pLabelSymbol; aLine, aCol: LongInt);
    constructor CreateGOTO( aLabel: pLabelSymbol; aLine, aCol: LongInt);

    constructor CopyCodeTree( CodeTree: pCodeTree);

    destructor Done; virtual;
  end;

implementation

uses AsmOpt, AsmCode;


constructor tCodeTree.CreateFunctionCall( aFuncTree, aRight, aSelfCode: pCodeTree;
      aLine, aCol: LongInt);
  begin
    inherited Init;
    Node.CodeType :=  cctFunctionCall;
    Line := aLine;
    Col := aCol;
    Left := aFuncTree;
    Right := aRight;
    Node.SelfCode := aSelfCode;
    if Assigned( aFuncTree) then
      begin
        ResType := aFuncTree^.ResType;
        if aFuncTree^.Node.CodeType = cctFunction then
          Node.CallType := aFuncTree^.Node.FuncSym^.Definition^.CallType
        else
          Node.CallType := pAbstractFunctionDefinition( ResType)^.CallType;
      end;
  end;

constructor tCodeTree.CreateOrdConst( Value: LongInt; Result: pDefinition; aLine, aCol: LongInt);
  begin
    Inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctOrdConst;
    if Assigned( Result) then
      case Result^.DefType of
        cOrdDefinition:
          if pOrdDefinition( Result)^.BaseType = cbtChar then
            Node.CodeType := cctCharConst
          else
            Node.CodeType := cctIntConst;
        cBooleanDefinition:
          Node.CodeType := cctBoolConst;
      end;
    Node.OrdValue := Value;
    Line := aLine;
    Col := aCol;
    ResType := Result;
  end;

constructor tCodeTree.CreateIntConst( Value: LongInt; Result: pDefinition; aLine, aCol: LongInt);
  begin
    Inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctIntConst;
    Node.IntValue := Value;
    Line := aLine;
    Col := aCol;
    ResType := Result;
  end;

constructor tCodeTree.CreatePointerConst( Value: LongInt; aSymbol: pSymbol;
    aName: pString; Result: pDefinition; aLine, aCol: LongInt);
  begin
    Inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctPointerConst;
    Node.PointerValue := Value;
    Node.PointerSymbol := aSymbol;
    Node.PointerName := aName;
    Line := aLine;
    Col := aCol;
    ResType := Result;
  end;

constructor tCodeTree.CreateCharConst( Value: Char; Result: pDefinition; aLine, aCol: LongInt);
  begin
    Inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctCharConst;
    Node.CharValue := Value;
    Line := aLine;
    Col := aCol;
    ResType := Result;
  end;

constructor tCodeTree.CreateRealConst( Value: Extended; Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init;
    Node.CodeType := cctRealConst;
    Node.RealValue := Value;
    Line := aLine;
    Col := aCol;
    ResType := Result;
  end;

constructor tCodeTree.CreateStringConst( const Value: String; Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init;
    Node.CodeType := cctStringConst;
    if Assigned( Result) and (Result^.DefType = cPointerDefinition) and
      Assigned( pPointerDefinition( Result)^.DefinitionType) and
      (pPointerDefinition( Result)^.DefinitionType^.DefType = cOrdDefinition) and
      (pOrdDefinition( pPointerDefinition( Result)^.DefinitionType)^.BaseType = cbtChar) then
      Node.CodeType := cctPCharConst;
    GetMem( Node.StringValue, Length(Value) + 1);
    Node.StringValue^ := Value;
    Line := aLine;
    Col := aCol;
    ResType := Result;
  end;

constructor tCodeTree.CreateBoolConst( Value: Boolean; Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init;
    Node.CodeType := cctBoolConst;
    Node.BoolValue := Value;
    Line := aLine;
    Col := aCol;
    ResType := Result;
  end;

constructor tCodeTree.CreateSetConst( Value: tByteSet; Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctSetConst;
    New( Node.SetValue);
    Node.SetValue^ := Value;
    ResType := Result;
    Col := aCol;
    Line := aLine;
  end;

constructor tCodeTree.CreateAddition( aLeft, aRight: pCodeTree; Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctAddition;
    Line := aLine;
    Col := aCol;
    ResType := Result;
    Left := aLeft;
    Right := aRight;
  end;

constructor tCodeTree.CreateSubtraction( aLeft, aRight: pCodeTree; Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctSubtraction;
    Line := aLine;
    Col := aCol;
    ResType := Result;
    Left := aLeft;
    Right := aRight;
  end;

constructor tCodeTree.CreateMultiplication( aLeft, aRight: pCodeTree; Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctMultiplication;
    Line := aLine;
    Col := aCol;
    ResType := Result;
    Left := aLeft;
    Right := aRight;
  end;

constructor tCodeTree.CreateDivision( aLeft, aRight: pCodeTree; Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctDivision;
    Line := aLine;
    Col := aCol;
    ResType := Result;
    Left := aLeft;
    Right := aRight;
  end;

constructor tCodeTree.CreateDiv( aLeft, aRight: pCodeTree; Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctDiv;
    Line := aLine;
    Col := aCol;
    ResType := Result;
    Left := aLeft;
    Right := aRight;
  end;

constructor tCodeTree.CreateEqual( Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctEqual;
    Line := aLine;
    Col := aCol;
    ResType := Result;
  end;

constructor tCodeTree.CreateUnequal( Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctUnequal;
    Line := aLine;
    Col := aCol;
    ResType := Result;
  end;

constructor tCodeTree.CreateGreater( Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctGreater;
    Line := aLine;
    Col := aCol;
    ResType := Result;
  end;

constructor tCodeTree.CreateLess( Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctLess;
    Line := aLine;
    Col := aCol;
    ResType := Result;
  end;

constructor tCodeTree.CreateGreaterEq( Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctGreaterEq;
    Line := aLine;
    Col := aCol;
    ResType := Result;
  end;

constructor tCodeTree.CreateLessEq( Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctLessEq;
    Line := aLine;
    Col := aCol;
    ResType := Result;
  end;

constructor tCodeTree.CreateIN( Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctIN;
    Line := aLine;
    Col := aCol;
    ResType := Result;
  end;

constructor tCodeTree.CreateMod( aLeft, aRight: pCodeTree; Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctMod;
    Line := aLine;
    Col := aCol;
    ResType := Result;
    Left := aLeft;
    Right := aRight;
  end;

constructor tCodeTree.CreateNot( Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctNot;
    Line := aLine;
    Col := aCol;
    ResType := Result;
  end;

constructor tCodeTree.CreateNeg( Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctNeg;
    Line := aLine;
    Col := aCol;
    ResType := Result;
  end;

constructor tCodeTree.CreateAnd( Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctAnd;
    Line := aLine;
    Col := aCol;
    ResType := Result;
  end;

constructor tCodeTree.CreateShl( Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctShl;
    Line := aLine;
    Col := aCol;
    ResType := Result;
  end;

constructor tCodeTree.CreateShr( Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctShr;
    Line := aLine;
    Col := aCol;
    ResType := Result;
  end;

constructor tCodeTree.CreateOr( Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctOr;
    Line := aLine;
    Col := aCol;
    ResType := Result;
  end;

constructor tCodeTree.CreateXor( Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctXor;
    Line := aLine;
    Col := aCol;
    ResType := Result;
  end;

constructor tCodeTree.CreateAssignment( AsnType: tCodeType;
    Result: pDefinition; aLeft, aRight: pCodeTree; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := AsnType;
    Line := aLine;
    Col := aCol;
    ResType := Result;
    Left := aLeft;
    Right := aRight;
  end;

constructor tCodeTree.CreateExpression( Expr: pCodeTree; Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctExpression;
    ResType := Result;
    Line := aLine;
    Col := aCol;
    Right := Expr;
  end;

constructor tCodeTree.CreateBlock( aBlock: pCodeTree; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctBlock;
    Right := aBlock;
    Line := aLine;
    Col := aCol;
  end;

constructor tCodeTree.CreateVariable( aVar: pVariableSymbol; aLine, aCol: LongInt);
  begin
    inherited Init;
    Node.CodeType := cctVariable;
    Node.Symbol := aVar;
    Line := aLine;
    Col := aCol;
    if Assigned( aVar) then
      ResType := aVar^.Definition;
  end;

constructor tCodeTree.CreateFunction( aFunc: pFunctionSymbol; Result: pDefinition);
  begin
    inherited Init;
    Node.CodeType := cctFunction;
    Node.FuncSym := aFunc;
    ResType := Result;
  end;

constructor tCodeTree.CreateTypeConversion( aConv: tTypeConversion; Result: pDefinition);
  begin
    inherited Init;
    Node.CodeType := cctTypeConversion;
    Node.Conversion := aConv;
    ResType := Result;
  end;

constructor tCodeTree.CreateLoadValue( aCodeTree: pCodeTree; Offset: pCodeTree; Result: pDefinition);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctLoadValue;
    Left := aCodeTree;
    Right := Offset;
    ResType := Result;
  end;

constructor tCodeTree.CreateDeref( aLeft: pCodeTree; Result: pDefinition; aLine, aCol: LongInt);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctDeref;
    Line := aLine;
    Col := aCol;
    ResType := Result;
    Left := aLeft;
  end;

constructor tCodeTree.CreateFuncParam( aLeft, aRight: pCodeTree);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctFunctionParam;
    Left := aLeft;
    Right := aRight;
    if Assigned( Right) then
      ResType := Right^.ResType;
  end;

constructor tCodeTree.CreateLoadAddress( CodeTree: pCodeTree; Result: pDefinition);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctLoadAddress;
    Left := CodeTree;
    ResType := Result;
  end;

constructor tCodeTree.CreateFuncRet( Result: pDefinition);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctFuncRet;
    ResType := Result;
  end;

constructor tCodeTree.CreateAsmBlock( AsmBlock: Pointer);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctAsmBlock;
    Node.Block := AsmBlock
  end;

constructor tCodeTree.CreateIFBlock( aCondition, aIF, aELSE: pCodeTree);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctIFBlock;
    Right := aCondition;
    Node.IFBlock := aIF;
    Node.ELSEBlock := aELSE;
  end;

constructor tCodeTree.CreateWhileBlock( aCondition, aLoopBlock: pCodeTree);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctWhileBlock;
    Right := aCondition;
    Node.LoopBlock := aLoopBlock;
  end;

constructor tCodeTree.CreateRepeatUntilBlock( aCondition, aLoopBlock: pCodeTree);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctRepeatUntil;
    Right := aCondition;
    Node.LoopBlock := aLoopBlock;
  end;

constructor tCodeTree.CreateFORBlock( aCounter, aMin, aMax, aLoop: pCodeTree;
      aForward: Boolean);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctForBlock;
    Right := aLoop;
    Node.Min := aMin;
    Node.Max := aMax;
    Node.Counter := aCounter;
    Node.IsForward := aForward;
  end;

constructor tCodeTree.CreatePred( Expression: pCodeTree);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctPred;
    Left := Expression;
    if Assigned( Expression) then
      ResType := Expression^.ResType;
  end;

constructor tCodeTree.CreateSucc( Expression: pCodeTree);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctSucc;
    Left := Expression;
    if Assigned( Expression) then
      ResType := Expression^.ResType;
  end;

constructor tCodeTree.CreateInc( Variable, Increment: pCodeTree; Result: pDefinition);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctInc;
    Left := Variable;
    Right := Increment;
    ResType := Result;
  end;

constructor tCodeTree.CreateDec( Variable, Decrement: pCodeTree; Result: pDefinition);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctDec;
    Left := Variable;
    Right := Decrement;
    ResType := Result;
  end;


constructor tCodeTree.CreateLength( Expression: pCodeTree; Result: pDefinition);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctLength;
    Left := Expression;
    ResType := Result;
  end;


constructor tCodeTree.CreateAssign( aFile, aFileName: pCodeTree);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctAssign;
    Left := aFile;
    Right := aFileName;
  end;


constructor tCodeTree.CreateArithmetic( aSysSymbol: tSystemSymboltype;
      Expression: pCodeTree; Result: pDefinition);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctArithmeticFunction;
    Node.SysSymbolType := aSysSymbol;
    Left := Expression;
    ResType := Result;
  end;


constructor tCodeTree.CreateNewDispose( CodeType: tCodeType;
      Expression: pCodeTree; Result: pDefinition; aCDcode: pCodeTree);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := CodeType;
    Left := Expression;
    ResType := Result;
    Node.CDCode := aCDcode;
  end;


constructor tCodeTree.CreateAssigned( Expression: pCodeTree; Result: pDefinition);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctAssigned;
    Left := Expression;
    ResType := Result;
  end;


constructor tCodeTree.CreateConcat( Dest, Source: pCodeTree; Result: pDefinition);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctConcat;
    Left := Dest;
    Right := Source;
    ResType := Result;
  end;


constructor tCodeTree.CreateIncludeExclude( CodeType: tCodeType; Dest, Item: pCodeTree);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := CodeType;
    Left := Dest;
    Right := Item;
  end;


constructor tCodeTree.CreateWrite( aFileCode, aParams: pCodeTree);
  begin
    inherited Init;
    Node.CodeType := cctWrite;
    Left := aFileCode;
    Right := aParams;
  end;

constructor tCodeTree.CreateWriteLn( aFileCode, aParams: pCodeTree);
  begin
    inherited Init;
    Node.CodeType := cctWriteLn;
    Left := aFileCode;
    Right := aParams;
  end;

constructor tCodeTree.CreateRead( aFileCode, aParams: pCodeTree);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctRead;
    Left := aFileCode;
    Right := aParams;
  end;

constructor tCodeTree.CreateReadLn( aFileCode, aParams: pCodeTree);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctReadLn;
    Left := aFileCode;
    Right := aParams;
  end;

constructor tCodeTree.CreateWriteParam( aExpression: pCodeTree;
      aLen, aDigs: pCodeTree);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctWriteParam;
    Right := aExpression;
    if Assigned( aExpression) then
      ResType := aExpression^.ResType;
    Node.Len := aLen;
    Node.Digs := aDigs;
  end;


constructor tCodeTree.CreateTypeOfExpression( anExpression: pCodeTree; aResType: pDefinition);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctTypeOfExpression;
    Left := anExpression;
    ResType := aResType;
  end;

constructor tCodeTree.CreateTypeOfType( anObjectDef: pObjectDefinition; aResType: pDefinition);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctTypeOfType;
    Node.ObjectDef := anObjectDef;
    ResType := aResType;
  end;


constructor tCodeTree.CreateCASEBlock( aExpression, aBlock, aElseBlock: pCodeTree);
   begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctCASEBlock;
    Node.Expression := aExpression;
    Right := aBlock;
    Node.ElseStatement := aElseBlock;
  end;

constructor tCodeTree.CreateCASENode( aCondition, aStatement, aLeft: pCodeTree);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctCASENode;
    Node.Statement := aStatement;
    Right := aCondition;
    Left := aLeft;
  end;

constructor tCodeTree.CreateCaseEqual( aValue: LongInt; aLeft: pCodeTree);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctCASEEqual;
    Node.Value := aValue;
    Left := aLeft;
  end;

constructor tCodeTree.CreateCaseBetween( aMin, aMax: LongInt; aLeft: pCodeTree);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctCASEBetween;
    Node.MinValue := aMin;
    Node.MaxValue := aMax;
    Left := aLeft;
  end;


constructor tCodeTree.CreateBREAK;
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctBreak;
  end;

constructor tCodeTree.CreateCONTINUE;
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctContinue;
  end;


constructor tCodeTree.CreateEXIT;
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctEXIT;
  end;


constructor tCodeTree.CreateWITHBlock( anExpression, aBlock: pCodeTree);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctWITHBlock;
    Node.WithBlock := aBlock;
    Right := anExpression;
  end;

constructor tCodeTree.CreateWithSymbol( aLevel: LongInt; Offset: pCodeTree;
    aResult: pDefinition);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctWithSymbol;
    Node.IntValue := aLevel;
    Left := Offset;
    ResType := aResult;
  end;


constructor tCodeTree.CreateSetItem( aItem: pCodeTree; Result: pDefinition);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctSetItem;
    Left := aItem;
    ResType := Result;
  end;

constructor tCodeTree.CreateSetRange( aMin, aMax: pCodeTree; Result: pDefinition);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := cctSetRange;
    Left := aMin;
    Right := aMax;
    ResType := Result;
  end;


constructor tCodeTree.CreateMemPort( aCodeType: tCodeType; aLeft: pCodeTree;
  aResult: pDefinition);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    Node.CodeType := aCodeType;
    Left := aLeft;
    ResType := aResult;
  end;

constructor tCodeTree.CreateLabel( aLabel: pLabelSymbol; aLine, aCol: LongInt);
  begin
    inherited Init;
    Node.CodeType := cctLabel;
    Node.LabelSymbol := aLabel;
    Line := aLine;
    Col := aCol;
  end;

constructor tCodeTree.CreateGOTO( aLabel: pLabelSymbol; aLine, aCol: LongInt);
  begin
    inherited Init;
    Node.CodeType := cctGOTO;
    Node.LabelSymbol := aLabel;
    Line := aLine;
    Col := aCol;
  end;

constructor tCodeTree.CopyCodeTree( CodeTree: pCodeTree);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    if Assigned( CodeTree) then
      begin
        Node.CodeType := CodeTree^.Node.CodeType;
        Line := CodeTree^.Line;
        Col := CodeTree^.Col;
        ResType := CodeTree^.ResType;
        case Node.CodeType of
          cctFunctionCall:
            begin
              Node.FuncSym := CodeTree^.Node.FuncSym;
              if Assigned( CodeTree^.Left) then
                Left := New( pCodeTree, CopyCodeTree( CodeTree^.Left));
            end;
          cctOrdConst:
            Node.OrdValue := CodeTree^.Node.OrdValue;
          cctRealConst:
            Node.RealValue := CodeTree^.Node.RealValue;
          cctIntConst:
            Node.IntValue := CodeTree^.Node.IntValue;
          cctCharConst:
            Node.CharValue := CodeTree^.Node.CharValue;
          cctStringConst,
          cctPCharConst:
            if Assigned( CodeTree^.Node.StringValue) then
              Node.StringValue := NewStr( CodeTree^.Node.StringValue^);
          cctSetConst:
            begin
              if Assigned( CodeTree^.Node.SetValue) then
                begin
                  New( Node.SetValue);
                  Node.SetValue^ := CodeTree^.Node.SetValue^;
                end;
              if Assigned( CodeTree^.ResType) then
                begin
                  ResType := New( pSetDefinition, Init(
                    pSetDefinition( CodeTree^.ResType)^.SetDef ));
                end;
            end;
          cctSetItem,
          cctSetRange:
            begin
              if Assigned( CodeTree^.Left) then
                Left := New( pCodeTree, CopyCodeTree( CodeTree^.Left));
              if Assigned( CodeTree^.Right) then
                Right := New( pCodeTree, CopyCodeTree( CodeTree^.Right));
              if Assigned( CodeTree^.ResType) then
                begin
                  ResType := New( pSetDefinition, Init(
                    pSetDefinition( CodeTree^.ResType)^.SetDef ));
                end;
            end;
          cctBoolConst:
            Node.BoolValue := CodeTree^.Node.BoolValue;
          cctLoadValue,
          cctExpression,
          cctBlock,
          cctFunctionParam,
          cctAddition, cctSubtraction, cctMultiplication, cctDivision, cctDiv,
          cctMod, cctAnd, cctShr, cctShl, cctOr, cctXor, cctNot, cctAssignment,
          cctEqual, cctUnequal, cctGreater, cctLess, cctGreaterEq, cctLessEq:
            begin
              if Assigned( CodeTree^.Left) then
                Left := New( pCodeTree, CopyCodeTree( CodeTree^.Left));
              if Assigned( CodeTree^.Right) then
                Right := New( pCodeTree, CopyCodeTree( CodeTree^.Right));
            end;
          cctTypeConversion:
            begin
              if Assigned( CodeTree^.Left) then
                Left := New( pCodeTree, CopyCodeTree( CodeTree^.Left));
              if Assigned( CodeTree^.Right) then
                Right := New( pCodeTree, CopyCodeTree( CodeTree^.Right));
              Node.Conversion := CodeTree^.Node.Conversion;
            end;
          cctVariable:
            Node.Symbol := CodeTree^.Node.Symbol;
          cctDeref:
            if Assigned( CodeTree^.Left) then
              Left := New( pCodeTree, CopyCodeTree( CodeTree^.Left));
          cctLoadAddress:
            if Assigned( CodeTree^.Left) then
              Left := New( pCodeTree, CopyCodeTree( CodeTree^.Left));
          cctCASEBlock:
            begin
              if Assigned( CodeTree^.Left) then
                Left := New( pCodeTree, CopyCodeTree( CodeTree^.Left));
              if Assigned( CodeTree^.Right) then
                Right := New( pCodeTree, CopyCodeTree( CodeTree^.Right));
              if Assigned( CodeTree^.Node.Expression) then
                Node.Expression := New( pCodeTree,
                  CopyCodeTree( CodeTree^.Node.Expression));
              if Assigned( CodeTree^.Node.ElseStatement) then
                Node.ElseStatement := New( pCodeTree, CopyCodeTree(
                  CodeTree^.Node.ElseStatement));
            end;
          cctCASENODE:
            begin
              if Assigned( CodeTree^.Left) then
                Left := New( pCodeTree, CopyCodeTree( CodeTree^.Left));
              if Assigned( CodeTree^.Right) then
                Right := New( pCodeTree, CopyCodeTree( CodeTree^.Right));
              if Assigned( CodeTree^.Node.Statement) then
                Node.Statement := New( pCodeTree, CopyCodeTree(
                  CodeTree^.Node.Statement));
            end;
          cctCASEEqual:
            begin
              if Assigned( CodeTree^.Left) then
                Left := New( pCodeTree, CopyCodeTree( CodeTree^.Left));
              if Assigned( CodeTree^.Right) then
                Right := New( pCodeTree, CopyCodeTree( CodeTree^.Right));
              Node.Value := CodeTree^.Node.Value;
            end;
          cctCASEBetween:
            begin
              if Assigned( CodeTree^.Left) then
                Left := New( pCodeTree, CopyCodeTree( CodeTree^.Left));
              if Assigned( CodeTree^.Right) then
                Right := New( pCodeTree, CopyCodeTree( CodeTree^.Right));
              Node.MinValue := CodeTree^.Node.MinValue;
              Node.MaxValue := CodeTree^.Node.MaxValue;
            end;
          cctWriteParam:
            begin
              if Assigned( CodeTree^.Left) then
                Left := New( pCodeTree, CopyCodeTree( CodeTree^.Left));
              if Assigned( CodeTree^.Right) then
                Right := New( pCodeTree, CopyCodeTree( CodeTree^.Right));
              if Assigned( CodeTree^.Node.Len) then
                Node.Len := New( pCodeTree, CopyCodeTree(
                  CodeTree^.Node.Len));
              if Assigned( CodeTree^.Node.Digs) then
                Node.Digs := New( pCodeTree, CopyCodeTree(
                  CodeTree^.Node.Digs));
            end;
          cctFuncRet:;
          cctAsmBlock:;
          cctIFBlock:;
          cctWhileBlock:;
          cctRepeatUntil:;
          cctForBlock:;
          cctCaseBlock:;
          cctBreak:;
          cctContinue:;
        end;
      end;
  end;

destructor tCodeTree.Done;
  begin
    if Assigned( Left) then
      Dispose( Left, Done{$IFDEF PPRO}(){$ENDIF});
    if Assigned( Right) then
      Dispose( Right, Done{$IFDEF PPRO}(){$ENDIF});

    case Location.Location of
      clMemory:
        if Assigned( Location.Reference.Symbol) then
          DisposeStr( Location.Reference.Symbol);
      clSymbol:
        if Assigned( Location.LabelName) then
          DisposeStr( Location.LabelName);
    end;

    case Node.CodeType of
      cctFunctionCall:
        if Assigned( Node.SelfCode) then
          Dispose( Node.SelfCode, Done{$IFDEF PPRO}(){$ENDIF});
      cctStringConst,
      cctPCharConst:
        if Assigned( Node.StringValue) then
          DisposeStr( Node.StringValue);
      cctSetConst:
        begin
          if Assigned( Node.SetValue) then
            Dispose( Node.SetValue);
          {if Assigned( ResType) and not Assigned( ResType^.Symbol) then
            Dispose( ResType, Done);}
        end;
      cctPointerConst:
        if Assigned( Node.PointerName) then
          DisposeStr( Node.PointerName);
      cctAsmBlock:
        if Assigned( Node.Block) then
          Dispose( pProcAsm(Node.Block), Done{$IFDEF PPRO}(){$ENDIF});
      cctIFBlock:
        begin
          if Assigned( Node.IFBlock) then
            Dispose( Node.IfBlock, Done{$IFDEF PPRO}(){$ENDIF});
          if Assigned( Node.ELSEBlock) then
            Dispose( Node.ELSEBlock, Done{$IFDEF PPRO}(){$ENDIF});
        end;
      cctWHILEBlock,
      cctRepeatUntil:
        if Assigned( Node.LoopBlock) then
          Dispose( Node.LoopBlock, Done{$IFDEF PPRO}(){$ENDIF});
      cctFORBlock:
        begin
          if Assigned( Node.Min) then
            Dispose( Node.Min, Done{$IFDEF PPRO}(){$ENDIF});
          if Assigned( Node.Max) then
            Dispose( Node.Max, Done{$IFDEF PPRO}(){$ENDIF});
          if Assigned( Node.Counter) then
            Dispose( Node.Counter, Done{$IFDEF PPRO}(){$ENDIF});
        end;
      cctCASEBlock:
        begin
          if Assigned( Node.Expression) then
            Dispose( Node.Expression, Done{$IFDEF PPRO}(){$ENDIF});
          if Assigned( Node.ElseStatement) then
            Dispose( Node.ElseStatement, Done{$IFDEF PPRO}(){$ENDIF});
        end;
      cctCASENode:
        begin
          if Assigned( Node.Statement) then
            Dispose( Node.Statement, Done{$IFDEF PPRO}(){$ENDIF});
        end;
      cctWriteParam:
        begin
          if Assigned( Node.Len) then
            Dispose( Node.Len, Done{$IFDEF PPRO}(){$ENDIF});
          if Assigned( Node.Digs) then
            Dispose( Node.Digs, Done{$IFDEF PPRO}(){$ENDIF});
        end;
      cctWithBlock:
        begin
          if Assigned( Node.WithBlock) then
            Dispose( Node.WithBlock, Done{$IFDEF PPRO}(){$ENDIF});
        end;
      cctNew,
      cctDispose:
        if Assigned( Node.CDcode) then
          Dispose( Node.CDcode, Done{$IFDEF PPRO}(){$ENDIF});
    end;

    if Assigned( ResType) and
      (DisposeType and cdtDisposeResult <> 0) then
        begin
          {Dispose( ResType, Done);}
          {ResType := nil;}
        end;

    inherited Done;
  end;


end.