{                    GNU GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Full text of license:
 https://www.gnu.org/licenses/gpl-3.0.en.html

 (c) Copyright 2022 DosWord
 (c) Copyright 1997-1998 Iggor Khachko - hachko@icl.kazan.su }

{
  + 13.2.98 added if..then..else
}

{$IFDEF TP}
{$X+,V-,G+,N+,E-,B-,T-}
{$IFDEF DEBUG}
{$I+,S+,R+,C+}
{$ELSE}
{$I-,S-,R-,C-}
{$ENDIF}
{$ENDIF}

unit PasComp;

interface

uses Dos, Objects, Config, Symbols, Scanner, Code, IAsm386, BasmComp, Tools;

type

  pCompiler = ^tCompiler;
  { Комплиятор паскалевских программ }
  tCompiler = object(tBasmCompiler)

    { Стандартные типы (чтобы их каждый раз не искать) }
    CharDef: pOrdDefinition;
    ShortDef: pOrdDefinition;
    ByteDef: pOrdDefinition;
    IntDef: pOrdDefinition;
    WordDef: pOrdDefinition;
    LongDef: pOrdDefinition;
    DWordDef: pOrdDefinition;
    ExtendedDef: pRealDefinition;
    StringDef: pStringDefinition;
    BoolDef: pBooleanDefinition;
    VoidDef: pDefinition;
    PointerDef: pPointerDefinition;
    UntypedFileDef: pFileDefinition;

    constructor Init( const aFileName: String; const aUnitName: tNameString);
    destructor Done; virtual;

    { Компилировать программу }
    procedure CompileProgram;
    { Компилировать модуль }
    procedure CompileUnit;

    { Компилировать метки }
    procedure ReadLabels( SymbolTable: pSymbolTable);
    { Компилировать типы }
    procedure ReadTypes( SymbolTable: pSymbolTable);
    { Компилирует константы }
    procedure ReadConsts( SymbolTable: pSymbolTable);
    { Компилирует переменные }
    function ReadVariables( SymbolTable: pSymbolTable; VType: tVariableType; BegOfs: LongInt): LongInt;
    { Кмпилирует Case-запись }
    function ReadCaseRecord( SymbolTable: pSymbolTable): LongInt;
    { Компилирует прцедуру }
    procedure ReadProcedure( SymbolTable: pSymbolTable; ObjectDef: pDefinition; OnlyHeader: Boolean);
    { Компилирует оператор }
    procedure ReadOperator( SymbolTable: pSymbolTable; OnlyHeader: Boolean);
    { Компилирует арифметической выражение }
    function ReadExpression( ResType: pDefinition): pCodeTree;
    { Компилирует отдельный оператор }
    procedure ReadStatement(var StatementCode: pCodeTree);
    { Компилирует параметры функции }
    procedure ReadFunctionParameters( FuncDef: pAbstractFunctionDefinition;
      MaxParam: LongInt; SymbolTable: pSymbolTable);
    { Компилирует заголовок функции }
    function ReadFunctionHeader( SymbolTable: pSymbolTable;
      ObjectDef: pDefinition; ProcOptions: LongInt): pFunctionSymbol;
    { Компилирует определение функции }
    procedure ReadProcedureDefinition(LocalSymbols: pSymbolTable);

    { Компилирует описание типа }
    function ReadTypeDefinition( TypeSymbol: pTypeSymbol; SymbolTable: pSymbolTable): pDefinition;
    { Компилирует описание процедурного типа }
    function ReadFunctionType( SymbolTable: pSymbolTable): pDefinition;

    { Создает системные типы }
    procedure CreateSystemTypes;
    { Считывает системные типы из модуля SYSTEM }
    procedure ReadSystemTypes;
    { Создает системные символы }
    procedure CreateSystemSymbols;

    function MakeFunctionCall( CodeTree: pCodeTree): pCodeTree;

    { Компилирует отдельный узел в арифметическом выражении }
    function GetCodeNode( ResultType: pDefinition): pCodeTree;

    function GetSymbolNode( Symbol: pSymbol; Level: LongInt;
      ResultType: pDefinition; SymbolTable: pSymbolTable): pCodeTree;

    { Компилирует вызов функции }
    function ReadFunctionCall( FuncName: tNameString; ObjectCode: pCodeTree;
      SymbolTable: pSymbolTable): pCodeTree;

    { Считывает значение для типизированной константы }
    function ReadTypedConstValue( TypeDef: pDefinition; var Value: tValue): Boolean;
    { Считывает значение массива }
    function ReadArrayConst( TypeDef: pArrayDefinition; var ValType: Integer): Pointer;
    { Счиывает значение записи }
    function ReadRecordConst( TypeDef: pRecordDefinition): Pointer;
    { Компилирует IF...THEN...ELSE }
    function ReadIfStatement: pCodeTree;
    { Компилирует WHILE...DO }
    function ReadWhileStatement: pCodeTree;
    {}
    function ReadRepeatUntilStatement: pCodeTree;
    {}
    function ReadForStatement: pCodeTree;
    {}
    function ReadCaseStatement: pCodeTree;
    {}
    function TranslateSystemSymbol( Symbol: pSystemSymbol): pCodeTree;
    {}
    function TranslateWrite( Symbol: tSystemSymbolType): pCodeTree;
    {}
    function TranslateRead( Symbol: tSystemSymbolType): pCodeTree;
    {}
    function TranslateSizeOf: pCodeTree;
    {}
    function TranslateChr: pCodeTree;
    {}
    function TranslateOrd: pCodeTree;
    {}
    function TranslatePredSucc( Symbol: tSystemSymbolType): pCodeTree;
    {}
    function TranslateStr: pCodeTree;
    {}
    function TranslateIncDec( Symbol: tSystemSymbolType): pCodeTree;
    {}
    function TranslateLength: pCodeTree;
    {}
    function TranslateOfs: pCodeTree;
    {}
    function ReadNew: pCodeTree;
    {}
    function ReadDispose: pCodeTree;
    {}
    function TranslateAssign: pCodeTree;
    {}
    function TranslateFloat( Symbol: tSystemSymbolType): pCodeTree;
    {}
    function TranslateOdd: pCodeTree;
    {}
    function TranslateAbs: pCodeTree;
    {}
    function TranslateAddr: pCodeTree;
    {}
    function TranslateAssigned: pCodeTree;
    {}
    function TranslateLow: pCodeTree;
    {}
    function TranslateHigh: pCodeTree;
    {}
    function TranslateConcat: pCodeTree;
    {}
    function TranslateIncludeExclude( CodeType: tCodeType): pCodeTree;
    {}
    function TranslateMemPort( CodeType: tCodeType;
      ResultType: pDefinition): pCodeTree;
    { Компилировать TypeOf }
    function TranslateTypeOf: pCodeTree;

    {}
    function ReadWithStatement: pCodeTree;

    {}
    function ReadObjectDefinition( TypeSymbol: pTypeSymbol; SymbolTable: pSymbolTable): pObjectDefinition;

    {}
    function ReadIfExpression( ResType: pDefinition): pCodeTree;
  end;


implementation

uses Errors, AsmCode, CodeOpt, Compiler, FileColl, StdLib;

constructor tCompiler.Init( const aFileName: String; const aUnitName: tNameString);
  begin
    inherited Init( aFileName, aUnitName);
    {UnitName := aUnitName;
    UnitSymbol^.SetName( UnitName);}
    CurrentFunction := nil;
    {GlobalSymbols := New(pSymbolTable, Init(stGlobalTable, 16, 16));}
    {LocalSymbols := nil;}
  end;

destructor tCompiler.Done;
  var
    FStack: pFunctionStack;
    I: Integer;
  begin
    FStack := CurrentFunction;
    while Assigned( CurrentFunction) do
      begin
        FStack := CurrentFunction;
        CurrentFunction := CurrentFunction^.Next;
        Dispose( FStack);
      end;
    if Assigned( MainFunc) then
      Dispose( MainFunc, Done);
    {if Assigned( StringDef) then
      Dispose( StringDef, Done);}
    if Assigned( UnitSymbol) then
      begin
        {if Assigned( UnitCollection) then
          if UnitCollection^.Search( UnitSymbol^.SymbolName, I) then
            UnitCollection^.AtFree( I);}
        Dispose( UnitSymbol, Done);
      end;
    inherited Done;
  end;

  procedure WriteMain( const Name: String; IsMain: Boolean);
    var
      Str: String;
    begin
      Str := AsmCompiler + ' ' +
               CreateAsmParam( Name) +
               _EOL_;
      BatchFile^.Write( Str[1], Length( Str));

      if IsMain then
        begin
          Str := Linker + ' ' +
            CreateLinkerParam( Name)
            + _EOL_;
          BatchFile^.Write( Str[1], Length( Str));
          if Stuber <> '' then
            begin
              Str := Stuber + ' ' +
                CreateStuberParam( Name) + _EOL_;
              BatchFile^.Write( Str[1], Length( Str));
            end;
        end;
    end;

procedure tCompiler.CompileProgram;

  procedure WriteObjFileName( S: pString); {$IFDEF TP} far; {$ENDIF}
    var
      Str: String;
    begin
{      if FindFile( S^, Str, ObjSearchPath) then
        begin}
        str := s^;
          if SeparateByEOL then
            Str := Str + _EOL_
          else
            Str := Str + ' ';
          if Assigned( ListFile) then
            ListFile^.Write( Str[ 1], Length( Str));
{        end;}
    end;

  procedure DoWrite( P: pUnitItem); {$IFDEF TP} far; {$ENDIF}
    var
      S: String;
    begin
      if Assigned( P^.LinkFiles) then
        P^.LinkFiles^.ForEach( @WriteObjFileName);
      if P^.IsUnitCompiled then
        begin
          S := P^.UnitName^ + ObjExt;
          {if Assigned( BatchList) then
            AsmList^.Write( S[1], Length( S));}
        end
      else
        if not FindFile( P^.UnitName^ + ObjExt,
          S, ObjSearchPath) then
            Exit
        else
          S := FExpand( S);
      if SeparateByEOL then
        S := S + _EOL_
      else
        S := S + ' ';
      if Assigned( ListFile) then
        ListFile^.Write( S[1], Length( S));
    end;

  var
    I: tIndex;

  begin
    if Assigned( UnitCollection) and UnitCollection^.Search( @UnitName, I) then
      pUnitItem( UnitCollection^.At( I))^.IsUnitCompiled := True;
    if Assigned( UnitSymbol) then
      begin
        Dispose( UnitSymbol, Done);
      end;
    UnitSymbol := nil;
    CreateMainProcedure( AsmSection^.GetValue( MainKey));
    CreateSystemTypes;
    CreateSystemSymbols;

    if LastToken = ctProgram then
      begin
        Consume( ctProgram);
        if LastToken <> ctIdentifier then
          Error( erIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
        GlobalSymbols^.Insert( New( pProgramSymbol, Init( LastLine, GlobalSymbols)));
        Consume( ctIdentifier);
        Consume( ctSemicolon);
      end;

    if LastToken = ctUses then
      LoadModules;

    ReadProcedureDefinition( GlobalSymbols);

    if LastToken <> ctPoint then
      begin
        Error(erUnexpectedEndOfFile, Files^.CurLine, Files^.CurCol, '');
        Exit;
      end;

    {GlobalSymbols^.Insert( MainFunc);}

    WriteAsmFile;

    UnitCollection^.ForEach( @DoWrite);
    LinkFiles^.ForEach( @WriteObjFileName);
    WriteMain( UnitName, True);
  end;

procedure tCompiler.CompileUnit;
  var
    S: pBufStream;
    Bool: Boolean;
    I: tIndex;
    UI: pUnitItem;
  begin
    IsUnit := True;
    SymbolsOptions := csoPublicSymbol;
    Consume( ctUnit);
    if Assigned( UnitCollection) and UnitCollection^.Search( @UnitName, I) then
      begin
        UI := pUnitItem( UnitCollection^.At( I));
        UI^.IsUnitCompiled := True;
        UI^.IsInterfaceReady := False;
        UI^.Compiler := @Self;
      end;
    if LastToken <> ctIdentifier then
      Error( erIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
    UnitName := LastLine;
    UnitSymbol^.SetName( UnitName);
    GlobalSymbols := pUnitSymbol(UnitSymbol)^.UnitSymbols;
    GlobalSymbols^.IsCompileInterface := True;

    CreateSystemTypes;
    CreateSystemSymbols;

    {GlobalSymbols^.Insert( UnitSymbol);}
    Consume( ctIdentifier);
    Consume( ctSemicolon);
    Consume( ctINTERFACE);

    if LastToken = ctUses then
      LoadModules{$IFDEF PPRO}(){$ENDIF};
    if not Assigned( Files) then
      Exit;

    while True do
      begin
        case LastToken of
          ctCONST:
            ReadConsts( GlobalSymbols);
          ctTYPE:
            ReadTypes( GlobalSymbols);
          ctVAR:
            begin
              Consume( ctVar);
              ReadVariables( GlobalSymbols, cvtGlobal, 0);
            end;
          ctPROCEDURE,
          ctFUNCTION:
            ReadProcedure( GlobalSymbols, nil, True);
          {ctFUNCTION:
            ReadFunction( GlobalSymbols, nil, True);}
          ctOPERATOR:
            ReadOperator( GlobalSymbols, True);
          else
            break;
        end;
      end;

    Consume( ctIMPLEMENTATION);
    UI^.IsInterfaceReady := True;
    SymbolsOptions := 0;
    GlobalSymbols^.IsCompileInterface := False;

    if LastToken = ctUses then
      LoadModules;

    while True do
      begin
        case LastToken of
          ctCONST:
            ReadConsts( GlobalSymbols);
          ctTYPE:
            ReadTypes( GlobalSymbols);
          ctVAR:
            begin
              Consume( ctVar);
              ReadVariables( GlobalSymbols, cvtGlobal, 0);
            end;
          ctPROCEDURE,
          ctFUNCTION,
          ctCONSTRUCTOR,
          ctDESTRUCTOR:
            ReadProcedure( GlobalSymbols, nil, False);
          ctOPERATOR:
            ReadOperator( GlobalSymbols, False);
          else
            break;
        end;
      end;

    if LastToken <> ctBEGIN then
      Consume( ctEND)
    else
      begin
        S := New( pBufStream, Init( UnitSymbol^.SymbolName^ +
          UnitExt, stOpen, 1024));
        S^.Seek( GlobalSymbols^.HasInitOffset);
        Bool := True;
        S^.Write( Bool, SizeOf( Bool));
        Dispose( S ,Done);
        GlobalSymbols^.HasInit := True;
        New( CurrentFunction);
        CurrentFunction^.Next := nil;
        CurrentFunction^.Func := New( pFunctionSymbol, Init( 'init', False,
          csoPublicSymbol));
        CurrentFunction^.Func^.Definition := New( pFunctionDefinition,
          Init( nil, 1, nil));
        ReadStatement( pCodeTree( CurrentFunction^.Func^.Definition^.Code));
        GlobalSymbols^.Insert( CurrentFunction^.Func);
        Dispose( CurrentFunction);
        CurrentFunction := nil;
      end;
    if LastToken <> ctPoint then
      Error( erUnexpectedEndOfFile, Files^.PrevLine, Files^.PrevCol, '');
    DeleteFile;
    WriteAsmFile;
    WriteMain( UnitName, False);
    pUnitSymbol( UnitSymbol)^.WriteUnit( UnitName + UnitExt);
  end;

procedure tCompiler.ReadLabels( SymbolTable: pSymbolTable);
  var
    Symbol: pSymbol;
  begin
    Consume( ctLabel);
    if LastToken <> ctIdentifier then
      Error( erIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
    repeat
      Symbol := SymbolTable^.Search( LastLine);
      if Assigned( Symbol) then
        Error( erDuplicateIdentifier, Files^.PrevLine, Files^.PrevCol, LastLine);
      SymbolTable^.Insert( New( pLabelSymbol, Init( LastLine, SymbolsOptions)));
      if NextToken <> ctComma then
        break;
      Consume( ctComma);
    until False;
    Consume( ctSemicolon);
  end;

procedure tCompiler.ReadConsts( SymbolTable: pSymbolTable);
  var
    ConstName: String;
    Expr: pCodeTree;
    L, Col: LongInt;
    TypeDef: pDefinition;
    Sym: pTypedConstSymbol;
    Value: tValue;
    P: pPointerValue;
  begin
    if Assigned( SymbolTable) then
    begin
      Consume( ctConst);
      repeat
        if LastToken = ctIdentifier then
          begin
            ConstName := LastLine;
            if FindLocalSymbol( ConstName) <> nil then
              begin
                Error( erDuplicateIdentifier, Files^.PrevLine, Files^.PrevCol, ConstName);
                Exit;
              end;
            if NextToken = ctEqual then
              begin
                Consume( ctEqual);
                L := Files^.PrevLine;
                Col := Files^.PrevCol;
                Expr := ReadExpression( nil);
                if not IsConst( Expr) then
                  Error( erCannotEvaluateThisExpression, L, Col, '');
                Consume( ctSemiColon);
                case Expr^.Node.CodeType of
                  cctIntConst:
                    Symboltable^.Insert( New( pConstSymbol, Init( ConstName,
                      cvOrdinalValue, Expr^.Node.IntValue,
                      Expr^.ResType, SymbolsOptions)));
                  cctRealConst:
                    Symboltable^.Insert( New( pConstSymbol, Init( ConstName,
                      cvRealValue, Expr^.Node.RealValue,
                      Expr^.ResType, SymbolsOptions)));
                  cctCharConst:
                    Symboltable^.Insert( New( pConstSymbol, Init( ConstName,
                      cvOrdinalValue, Expr^.Node.CharValue,
                      Expr^.ResType, SymbolsOptions)));
                  cctStringConst:
                    SymbolTable^.Insert( New( pConstSymbol, Init( ConstName,
                      cvStringValue, Expr^.Node.StringValue, Expr^.ResType, SymbolsOptions)));
                  cctOrdConst:
                    SymbolTable^.Insert( New( pConstSymbol, Init( ConstName,
                      cvOrdinalValue, Expr^.Node.OrdValue,
                      Expr^.ResType, SymbolsOptions)));
                  cctBoolConst:
                    SymbolTable^.Insert( New( pConstSymbol, Init( ConstName,
                      cvOrdinalValue, Expr^.Node.BoolValue,
                      Expr^.ResType, SymbolsOptions)));
                  cctSetConst:
                    begin
                      SymbolTable^.Insert( New( pConstSymbol, Init( ConstName,
                        cvSetValue, Expr^.Node.SetValue^,
                        Expr^.ResType, SymbolsOptions)));
                      Expr^.ResType := nil;
                    end;
                  cctPointerConst,
                  cctLoadAddress:
                    begin
                      P := CreatePointerValue( Expr);
                      SymbolTable^.Insert( New( pConstSymbol, Init( ConstName,
                        cvAddressValue, P,
                        Expr^.ResType, SymbolsOptions)));
                    end;
                end;
                Dispose( Expr, Done);
              end
            else if LastToken = ctColon then
              begin
                Consume( ctColon);
                TypeDef := ReadTypeDefinition( nil, SymbolTable);
                if Assigned( TypeDef) then
                  begin
                    Consume( ctEqual);
                    if ReadTypedConstValue( TypeDef, Value) then
                      begin
                        Sym := New( pTypedConstSymbol, Init( ConstName,
                          TypeDef, SymbolsOptions));
                        GlobalSymbols^.Insert( Sym);
                        Sym^.Value := Value;
                      end;
                  end;
                Consume( ctSemicolon);
              end
            else
              Error( erEqualExpected, Files^.PrevLine, Files^.PrevCol, '');
          end;
      until LastToken <> ctIdentifier;
    end;
  end;

procedure tCompiler.ReadTypes( SymbolTable: pSymbolTable);

  procedure DerefPointers( Symbol: pSymbol); {$IFDEF TP}far;{$ENDIF}
    var
      Def: pDefinition;
    begin
      if Symbol^._Type = cTypeSymbol then
        begin
        case pTypeSymbol( Symbol)^.Definition^.DefType of
          cPointerDefinition:
            begin
              Def := pTypeSymbol( Symbol)^.Definition;
              if not Assigned( pPointerDefinition( Def)^.DefinitionType) then
                if Assigned( pPointerDefinition( Def)^.DefSym) and
                  Assigned( pTypeSymbol(pPointerDefinition( Def)^.DefSym)^.Definition) then
                begin
                  pPointerDefinition(Def)^.DefinitionType :=
                    pTypeSymbol(pPointerDefinition( Def)^.DefSym)^.Definition;
                end
              else
                Error( erUndefinedTypeInPointerDefinition, Def^.Line, Def^.Col, '');
            end;
        end;
        end;
    end;

  var
    SType: pTypeSymbol;
    I: Integer;
    TypeName: String;
    Def: pDefinition;
  begin
    if not Assigned(SymbolTable) then
      Error( erInternalError, Files^.CurLine, Files^.CurCol, '');
    Consume( ctType);
    repeat
      Def := nil;
      if LastToken <> ctIdentifier then
        Error( erIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
      SType := pTypeSymbol( FindLocalSymbol( LastLine));
      if Assigned( SType) then
        begin
          if (SType^._Type <> cTypeSymbol) or
            Assigned( SType^.Definition) then
            Error( erDuplicateIdentifier, Files^.PrevLine, Files^.PrevCol, LastLine)
        end
      else
        begin
          SType := New( pTypeSymbol, Init( LastLine, nil, SymbolsOptions));
          SymbolTable^.Insert( SType);
        end;
      TypeName := LastLine;
      if NextToken{$IFDEF PPRO}(){$ENDIF} <> ctEqual then
        Error( erEqualExpected, Files^.PrevLine, Files^.PrevCol, '');
      Consume( ctEqual);
      Def := ReadTypeDefinition( SType, SymbolTable);
      if Def^.DefType = cObjectDefinition then
        begin
          pObjectDefinition( Def)^.PublicSymbols^.Name :=
            NewStr( 'U$' + UnitName + '$_$' + TypeName + '$');
          {SType := pTypeSymbol( Def^.Symbol);}
        end;
      if not Assigned( SType) then
        begin
          {SType := New( pTypeSymbol, Init( TypeName, Def, SymbolsOptions));
          SymbolTable^.Insert(SType);}
        end
      else
        begin
          SType^.Definition := Def;
          if not Assigned( Def^.Symbol) then
            begin
              Def^.Symbol := SType;
              SType^.IsOwner := True;
            end;
        end;
      SType^.Owner := SymbolTable;
      Consume( ctSemiColon);
    until LastToken <> ctIdentifier;
    SymbolTable^.ForEach( @DerefPointers);
  end;

type
    pStringList = ^tStringList;
    tStringList = record
      Str: String;
      Line, Col: LongInt;
      Next: pStringList;
    end;

function tCompiler.ReadVariables( SymbolTable: pSymbolTable; VType: tVariableType; BegOfs: LongInt): LongInt;
  var
    NList, CurItem: pStringList;
    I: Integer;
    TypeDef: pDefinition;
    VSym: pVariableSymbol;
    Offset: LongInt;
    IsAbsolute: Boolean;
    AbsType: tAbsoluteType;
    Ref: pSymbol;
    L: LongInt;
    W: Integer;
  begin
    Offset := 0;
    repeat
      NList := nil;
      repeat
        if NList = nil then
          begin
            New( NList);
            CurItem := NList;
          end
        else
          begin
            New( CurItem^.Next);
            CurItem := CurItem^.Next;
            NextToken;
          end;
        if LastToken <> ctIdentifier then
          Error( erIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
        CurItem^.Next := nil;
        CurItem^.Str := LastLine;
        CurItem^.Line := Files^.PrevLine;
        CurItem^.Col := Files^.PrevCol;
      until NextToken <> ctComma;
      if LastToken <> ctColon then
        Error( erColonExpected, Files^.PrevLine, Files^.PrevCol, '');
      if NextToken{$IFDEF PPRO}(){$ENDIF} in [ ctObject, ctClass] then
        Error( erErrorInType, Files^.PrevLine, Files^.PrevCol, '');

      TypeDef := nil;
      TypeDef := ReadTypeDefinition( nil, SymbolTable);

      {writeln( ord( vtype));
      writeln( ord( lasttoken), '"', lastline, '"');}
      IsAbsolute := False;
      if ((VType = cvtLocal) or (VType = cvtGLobal)) and
        (LastToken = ctAbsolute) then
        begin
          Consume( ctAbsolute);
          case LastToken of
            ctIntConst:
              begin
                AbsType := catAddress;
                Val( LastLine, LongInt( Ref), W);
                NextToken;
              end;
            ctIdentifier:
              begin
                AbsType := catVariable;
                Ref := FindSymbol( LastLine, L);
                if not Assigned( Ref) then
                  Error( erUnknownIdentifier, Files^.PrevLine, Files^.PrevCol, LastLine);
                if ((Ref^._Type <> cVariableSymbol) and
                  (Ref^._Type <> cTypedConstSymbol)) or
                  (pVariableSymbol( Ref)^.VarType = cvtField) then
                  Error( erVariableIdentifierExpected, Files^.PrevLine, Files^.PrevCol, LastLine);
                NextToken;
              end;
            else
              Error( erErrorInExpression, Files^.PrevLine, Files^.PrevCol, '');
          end;
          IsAbsolute := True;
        end;

      while Assigned(NList) do
        begin
          if SymbolTable^.FindSymbol( NList^.Str) <> nil then
            Error( erDuplicateIdentifier, NList^.Line, NList^.Col, NList^.Str);
          if IsAbsolute then
            begin
              VSym := New( pAbsoluteSymbol, Init( NList^.Str, TypeDef, VType,
                SymbolsOptions, AbsType, pVariableSymbol( Ref)));
            end
          else
            begin
              VSym := New( pVariableSymbol, Init( NList^.Str, TypeDef, VType, SymbolsOptions));
              case VType of
                cvtLocal:
                  begin
                    Dec( Offset, (TypeDef^.GetSize + 3) and not 3 );
                    VSym^.Offset := Offset - BegOfs;
                  end;
                cvtParam:
                  if TypeDef^.GetSize and 3 = 0 then
                    Inc( Offset, TypeDef^.GetSize)
                  else
                    Inc( Offset, (TypeDef^.GetSize and (not 3)) + 4);
                cvtVarParam,
                cvtConstParam,
                cvtStringParam:
                    Inc( Offset, 4);
                cvtField:
                  begin
                    VSym^.Offset := Offset + BegOfs;
                    Inc( Offset, TypeDef^.GetSize);
                  end;
              end;
            end;
          SymbolTable^.Insert( VSym);
          CurItem := NList;
          NList := NList^.Next;
          Dispose( CurItem);
        end;
      if LastToken <> ctSemiColon then
        break;
      NextToken{$IFDEF PPRO}(){$ENDIF};
    until LastToken <> ctIdentifier;
    ReadVariables := Abs( Offset);
  end;

procedure tCompiler.ReadFunctionParameters( FuncDef: pAbstractFunctionDefinition;
    MaxParam: LongInt; SymbolTable: pSymbolTable);
  const
    CurOffset: LongInt = 0;
  var
    VarType: tVariableType;
    VarSym: pVariableSymbol;
    Size, CurParam: LongInt;
    Str: String;
    LocalTable: pSymbolTable;

  procedure CreateOffset( P: pVariableSymbol); {$IFDEF TP}far;{$ENDIF}
    begin
      if P^._Type = cVariableSymbol then
        begin
          if P^.VarType = cvtParam then
            if P^.Size{$IFDEF PPRO}(){$ENDIF} and 3 = 0 then
              Dec( CurOffset, P^.Size{$IFDEF PPRO}(){$ENDIF})
            else
              Dec( CurOffset, (P^.Size{$IFDEF PPRO}(){$ENDIF} and not 3) + 4 )
          else
            Dec( CurOffset, 4);
          P^.Offset := CurOffset;
        end;
    end;

    var
      NList, CurItem: pStringList;
      I: tIndex;
      TypeDef: pDefinition;
      VSym: pVariableSymbol;
      ParamColl: pDefCollection;
      Line, Col: LongInt;
      LocalSymbols: pSymbolTable;
    begin
      Size := 0;
      CurParam := 0;
      if FuncDef^.DefType = cFunctionDefinition then
        LocalSymbols := pFunctionDefinition( FuncDef)^.LocalSymbols
      else
        LocalSymbols := New( pSymbolTable, Init( stParamTable, 5, 5));
      if CurLevel > 1 then
        begin
          Inc( Size, 4);
        end;
      if NextToken{$IFDEF PPRO}(){$ENDIF} = ctLParen then
        begin
          Consume( ctLParen);
          repeat
            VarType := cvtParam;
            if LastToken = ctVar then
              begin
                Consume( ctVar);
                VarType := cvtVarParam;
              end
            else if LastToken = ctConst then
              begin
                Consume( ctConst);
                VarType := cvtConstParam;
              end;

            if LastToken = ctIdentifier then
              begin
                NList := nil;
                repeat
                  if NList = nil then
                    begin
                      New( NList);
                      CurItem := NList;
                    end
                  else
                    begin
                      New( CurItem^.Next);
                      CurItem := CurItem^.Next;
                      NextToken{$IFDEF PPRO}(){$ENDIF};
                    end;
                  Inc( CurParam);
                  if CurParam > MaxParam then
                    Error( erRightParenExpected, Files^.PrevLine, Files^.PrevCol, '');
                  if LastToken <> ctIdentifier then
                    Error( erIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
                  CurItem^.Next := nil;
                  CurItem^.Str := LastLine;
                  CurItem^.Line := Files^.PrevLine;
                  CurItem^.Col := Files^.PrevCol;
                until NextToken{$IFDEF PPRO}(){$ENDIF} <> ctComma;
                {if LastToken <> ctColon then
                  Error( erColonExpected, CurLine, LastCol);
                NextToken;}
                if (LastToken = ctColon) or (VarType <> cvtVarParam) then
                  begin
                    Consume( ctColon);

                    TypeDef := nil;
                    case LastToken of
                      ctIdentifier:
                        begin
                          Line := Files^.PrevLine;
                          Col := Files^.PrevCol;
                          TypeDef := ReadTypeDefinition( nil, SymbolTable);
                          if not Assigned( TypeDef) or
                            not Assigned( TypeDef^.Symbol) then
                            Error( erTypeIdentifierExpected, Line, Col, '');
                          if (TypeDef^.DefType = cFileDefinition) and
                            (VarType <> cvtVarParam) then
                            Error( erFilesMustBeVarParameters, Line, Col, '');
                        end;
                      ctString:
                        begin
                          TypeDef := StringDef;
                          Consume( ctString);
                        end;
                      ctFile:
                        begin
                          TypeDef := UntypedFileDef;
                          Consume( ctFile);
                          if (VarType <> cvtVarParam) then
                            Error( erFilesMustBeVarParameters, Line, Col, '');
                        end;
                      else
                        Error( erTypeIdentifierExpected, Line, Col, '');
                    end;
                    if TypeDef^.DefType = cStringDefinition then
                      if VarType = cvtParam then
                        VarType := cvtStringParam;
                  end
                else
                  begin
                    TypeDef := VoidDef;
                  end;

                if LastToken <> ctRParen then
                  Consume( ctSemicolon);

                while Assigned(NList) do
                  begin
                    if LocalSymbols^.Search( NList^.Str) <> nil then
                      Error( erDuplicateIdentifier, NList^.Line, NList^.Col, NList^.Str);
                    New( ParamColl);
                    ParamColl^.Definition := TypeDef;
                    ParamColl^.ParamType := VarType;
                    ParamColl^.Next := FuncDef^.ParamColl;
                    FuncDef^.ParamColl := ParamColl;
                    VSym := New( pVariableSymbol, Init( NList^.Str, TypeDef, VarType, 0));
                    if VarType <> cvtParam then
                      Inc( Size, 4)
                    else
                      if TypeDef^.GetSize{$IFDEF PPRO}(){$ENDIF} and 3 = 0 then
                        Inc( Size, TypeDef^.GetSize{$IFDEF PPRO}(){$ENDIF})
                      else
                        Inc( Size, (TypeDef^.GetSize{$IFDEF PPRO}(){$ENDIF} and (not 3)) + 4);
                    LocalSymbols^.Insert( VSym);
                    CurItem := NList;
                    NList := NList^.Next;
                    Dispose( CurItem);
                  end;
              end
            else
              Error( erIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
         until LastToken = ctRParen;
         CurOffset := Size + 8;
         LocalSymbols^.ForEach( @CreateOffset);
         Consume( ctRParen);
        end;
      pAbstractFunctionDefinition( FuncDef)^.ParamSize := Size;
      if FuncDef^.DefType <> cFunctionDefinition then
        Dispose( LocalSymbols, Done);
    end;

function tCompiler.ReadFunctionHeader( SymbolTable: pSymbolTable;
    ObjectDef: pDefinition; ProcOptions: LongInt): pFunctionSymbol;
  var
    FuncSym: pFunctionSymbol;
    VarType: tVariableType;
    VarSym: pVariableSymbol;
    Size: LongInt;
    Str: String;
  begin
    FuncSym := nil;
    if LastToken = ctIdentifier then
      begin
        FuncSym := New( pFunctionSymbol, Init( LastLine, False, SymbolsOptions));
        FuncSym^.Definition := New( pFunctionDefinition, Init( nil,
          CurLevel, pObjectDefinition( ObjectDef) ));
        FuncSym^.Definition^.Symbol := FuncSym;
        if ProcOptions and poDestructor = 0 then
          ReadFunctionParameters(FuncSym^.Definition, 255, SymbolTable)
        else
          NextToken;
        if Assigned( ObjectDef) then
          begin
            FuncSym^.Definition^.ProcOptions :=
              FuncSym^.Definition^.ProcOptions or poMethod or ProcOptions;
            VarSym :=
              New( pVariableSymbol, Init( SelfName, ObjectDef, cvtVarParam, 0));
            VarSym^.Offset := FuncSym^.Definition^.ParamSize + 8;
            VarSym^.IsOwner := False;
            FuncSym^.Definition^.LocalSymbols^.Insert( VarSym);
            Inc( FuncSym^.Definition^.ParamSize, 4);
          end;
        FuncSym^.Definition^.LocalSymbols^.Name :=
          NewStr( GetSymbolTableName +
            FuncSym^.Name + '_');
      end
    else
      Error( erIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
    ReadFunctionHeader := FuncSym;
  end;

procedure tCompiler.ReadProcedure( SymbolTable: pSymbolTable;
    ObjectDef: pDefinition; OnlyHeader: Boolean);
  var
    Sym, ProcSym: pFunctionSymbol;
    FuncStack: pFunctionStack;
    Pos: tIndex;
    ProcOptions: LongInt;
    ReadResult: Boolean;
    Result: pVariableSymbol;
    ForwardAllowed: Boolean;
  begin
    ForwardAllowed := not OnlyHeader;
    ReadResult := False;
    Inc( CurLevel);
    case LastToken of
      ctProcedure:
        ProcOptions := poNormal;
      ctConstructor:
        ProcOptions := poConstructor;
      ctDestructor:
        ProcOptions := poDestructor;
      ctFunction:
        begin
          ProcOptions := poNormal;
          ReadResult := True;
        end;
    end;
    NextToken;
    if LastToken <> ctIdentifier then
      Error( erIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
    Sym := pFunctionSymbol(FindLocalSymbol( LastLine));
    if Assigned( Sym) and( Sym^._Type = cTypeSymbol) and
      (pTypeSymbol( Sym)^.Definition^.DefType = cObjectDefinition) then
      begin
        ObjectDef := pTypeSymbol( Sym)^.Definition;
        SymbolTable := pObjectDefinition( ObjectDef)^.PublicSymbols;
        Consume( ctIdentifier);
        Consume( ctPoint);
        if LastToken <> ctIdentifier then
          Error( erIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
        Sym := pFunctionSymbol( SymbolTable^.FindSymbol( LastLine));
        if not Assigned( Sym) or (Sym^._Type <> cFunctionSymbol) then
          Error( erMethodIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
      end;
    if (ProcOptions <> poNormal) and not Assigned( ObjectDef) then
      Error( erObjectTypeExpected, Files^.PrevLine, Files^.PrevCol, '');
    if Assigned( Sym) and (Sym^._Type <> cFunctionSymbol) then
      Error( erDuplicateIdentifier, Files^.PrevLine, Files^.PrevCol, LastLine);
    ProcSym := ReadFunctionHeader( SymbolTable, ObjectDef, ProcOptions);
    {ProcSym^.Definition^.ProcOptions := ProcSym^.Definition^.ProcOptions or
      ProcOptions;}

    if ReadResult then
      begin
        Consume( ctColon);
        if not ( LastToken in [ctIdentifier, ctString]) then
          Error( erTypeIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
        ProcSym^.Definition^.ResType := ReadTypeDefinition( nil, SymbolTable);

        case pFunctionSymbol(ProcSym)^.Definition^.ResType^.DefType of
          cOrdDefinition,
          cUserOrdDefinition,
          cBooleanDefinition,
          cPointerDefinition:
            begin
              Result := New( pVariableSymbol, Init( FuncResultName, ProcSym^.Definition^.ResType, cvtLocal, 0));
              Inc( ProcSym^.Definition^.LocalSymbols^.DataSize, 4);
              Result^.Offset := - ProcSym^.Definition^.LocalSymbols^.DataSize;
            end;
          cRealDefinition:
            begin
              Result := New( pVariableSymbol, Init( FuncResultName, ProcSym^.Definition^.ResType, cvtLocal, 0));
              Inc( ProcSym^.Definition^.LocalSymbols^.DataSize,
                Result^.Definition^.GetSize{$IFDEF PPRO}(){$ENDIF});
              Result^.Offset := - ProcSym^.Definition^.LocalSymbols^.DataSize;
            end;
          else
            begin
              Result := New( pVariableSymbol, Init( FuncResultName, ProcSym^.Definition^.ResType, cvtVarParam, 0));
              Result^.Offset := ProcSym^.Definition^.ParamSize + 8;
              {Size := pVariableSymbol(Sym)^.Definition^.GetSize;
              if Size and 3 <> 0 then
                Size := Size and not 3 + 4;}
              Inc( ProcSym^.Definition^.ParamSize, 4);
            end;
        end;
        ProcSym^.Definition^.LocalSymbols^.Insert( Result);
      end;

    Sym := SymbolTable^.Search( ProcSym^.SymbolName^);
    if not Assigned( Sym) then
      SymbolTable^.Insert( ProcSym)
    else
      begin
        if Sym^._Type <> cFunctionSymbol then
          Error( erDuplicateIdentifier, Files^.PrevLine, Files^.PrevCol, ProcSym^.SymbolName^)
        else
          begin
            while Assigned( Sym^.NextOverloaded) do
              begin
                if IsSameParams( Sym^.Definition^.ParamColl,
                  ProcSym^.Definition^.ParamColl) then
                    break;
                Sym := Sym^.NextOverloaded;
              end;
            ProcSym^.NextOverloaded := nil;
            if IsSameParams( Sym^.Definition^.ParamColl,
              ProcSym^.Definition^.ParamColl) then
                if Assigned( Sym^.Definition^.Code) or OnlyHeader or
                  (Sym^.Definition^.ProcOptions and poExternal <> 0) then
                  Error( erOverloadedFunctionWithSamesParameters, Files^.PrevLine, Files^.PrevCol, ProcSym^.SymbolName^)
                else if not EqualHeaders( ProcSym, Sym) then
                  Error( erHeaderDoesNotMatchPreviousDefinition,
                    Files^.PrevLine,  Files^ .PrevCol, ProcSym^.SymbolName^)
                else
                  begin
                    ForwardAllowed := False;
                    if (Sym^.Definition^.ProcOptions and
                      (poConstructor + poDestructor) ) <> ProcOptions then
                      Error( erHeaderDoesNotMatchPreviousDefinition,
                        Files^.PrevLine, Files^.PrevCol,
                        ProcSym^.Name);
                    Dispose( ProcSym, Done);
                    ProcSym := Sym;
                    {CurrentFunction^.Func := ProcSym;}
                  end
            else if Assigned( ObjectDef) and not OnlyHeader then
              Error( erInvalidFunctionParameters, Files^.PrevLine, Files^.PrevCol,
                ProcSym^.SymbolName^)
            else
              begin
                Sym^.NextOverloaded := ProcSym;
                SymbolTable^.Insert( ProcSym);
                {ProcSym^.Owner := Sym^.Owner;}
              end;
          end;
      end;

    Consume( ctSemicolon);
    New( FuncStack);
    FuncStack^.Next := CurrentFunction;
    FuncStack^.Func := ProcSym;
    CurrentFunction := FuncStack;

    {if LastToken = ctStringConst then
      begin
      end;}

    if CurLevel <= 1 then
      SelfSymbol := pVariableSymbol( ProcSym^.Definition^.LocalSymbols^.FindSymbol( SelfName));
    PushTable( ProcSym^.Definition);
    while True do
      begin
        case LastToken of
          ctPASCAL:
            begin
              Consume( ctPASCAL);
              Consume( ctSemicolon);
              ProcSym^.Definition^.SetCallType( cctPascal);
            end;
          ctSTDCALL:
            begin
              Consume( ctSTDCALL);
              Consume( ctSemicolon);
              ProcSym^.Definition^.SetCallType( cctStdCall);
            end;
          ctCDECL:
            begin
              Consume( ctCDECL);
              Consume( ctSemicolon);
              ProcSym^.Definition^.SetCallType( cctCDecl);
            end;
          else
            break;
        end;
      end;
    if ProcSym^.Definition^.CallType = cctDefault then
      ProcSym^.Definition^.SetCallType( cctPascal);
    if not OnlyHeader then
      begin
        while True do
          begin
            case LastToken of
              ctStringConst:
                begin
                  if Assigned( ProcSym^.Alias) then
                    Error( erAliasAlreadyDefined, Files^.PrevLine, Files^.PrevCol, '');
                  ProcSym^.Alias := NewStr( Copy( LastLine, 2, Length( LastLine) - 2) );
                  Consume( ctStringConst);
                  Consume( ctSemicolon);
                  ForwardAllowed := False;
                end;
              ctEXTERNAL:
                begin
                  Consume( ctEXTERNAL);
                  if ProcSym^.Definition^.CallType = cctDefault then
                    ProcSym^.Definition^.SetCallType( cctPascal);
                  ProcSym^.Definition^.ProcOptions :=
                    ProcSym^.Definition^.ProcOptions or poExternal;
                  break;
                end;
              ctFORWARD:
                begin
                  if not ForwardAllowed then
                    Consume( ctBegin);
                  Consume( ctFORWARD);
                  break;
                end;
              ctASSEMBLER:
                begin
                  ProcSym^.Definition^.ProcOptions :=
                    ProcSym^.Definition^.ProcOptions or poAssembler;
                  Consume( ctAssembler);
                  Consume( ctSemicolon);
                  if ReadResult then
                    begin
                      Result := pVariableSymbol(
                        ProcSym^.Definition^.LocalSymbols^.FindSymbol( FuncResultName));
                      if Result^.Offset < 0 then
                        begin
                          if Result^.Definition^.GetSize{$IFDEF PPRO}(){$ENDIF} <= 4 then
                            Dec( ProcSym^.Definition^.LocalSymbols^.DataSize, 4)
                          else
                            Dec( ProcSym^.Definition^.LocalSymbols^.DataSize,
                              Result^.Definition^.GetSize{$IFDEF PPRO}(){$ENDIF});
                          Result^.Offset := 0;
                          Result^.IsRegisterable := True;
                          if Result^.Definition^.DefType = cRealDefinition then
                            Result^.Register := crST
                          else
                            Result^.Register := crEAX;
                        end;
                    end;
                end;
              else
                begin
                  if CurLevel <= 1 then
                    CurrentObject := pObjectDefinition( ObjectDef);
                  ReadProcedureDefinition( ProcSym^.Definition^.LocalSymbols);
                  if CurLevel <= 1 then
                    if Assigned( ObjectDef) then CurrentObject := nil;
                  break;
                end;
            end;
          end;
        Consume( ctSemicolon);
      end
    else if Assigned( ObjectDef) then
      if ( LastToken = ctVirtual ) then
        begin
          Consume( ctVirtual);
          Consume( ctSemicolon);
          pObjectDefinition( ObjectDef)^.MakeVirtual( ProcSym);
        end
      else if pObjectDefinition( ObjectDef)^.MustBeVirtual( ProcSym) then
        Consume( ctVirtual);

    if CurLevel <=1 then
      if Assigned( ObjectDef) then SelfSymbol := nil;
    Dec( CurLevel);
    PopTable;
    FuncStack := CurrentFunction;
    CurrentFunction := CurrentFunction^.Next;
    Dispose( FuncStack);

  end;


procedure tCompiler.ReadOperator( SymbolTable: pSymbolTable; OnlyHeader: Boolean);
  var
    Sym: pSymbol;
    Result: pVariableSymbol;
    OpSym: pOperatorSymbol;
    FuncStack: pFunctionStack;
    Pos: tIndex;
    Size: LongInt;
    OpType: tPasOperators;
    ResName: tNameString;
  begin
    Consume( ctOperator);
    Inc( CurLevel);
    OpType := GetOperatorType( LastToken);
    if (OpType = cpoUnknown) then
      Error( erUnknownOperator, Files^.PrevLine, Files^.PrevCol, LastLine);
    {NextToken;}
    OpSym := New( pOperatorSymbol, Init( OpType, SymbolsOptions));
    OpSym^.Definition := New( pFunctionDefinition, Init( nil, CurLevel, nil));
    OpSym^.Definition^.Symbol := OpSym;
    if OpType <> cpoNot then
      ReadFunctionParameters( OpSym^.Definition, 2, SymbolTable)
    else
      ReadFunctionParameters( OpSym^.Definition, 1, SymbolTable);
    OpSym^.Definition^.LocalSymbols^.Name :=
      NewStr( GetSymbolTableName{$IFDEF PPRO}(){$ENDIF} +
        OpSym^.Name{$IFDEF PPRO}(){$ENDIF} + '_');

    if LastToken <> ctIdentifier then
      Error( erIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
    if OpSym^.Definition^.LocalSymbols^.Search( LastLine) <> nil then
      Error( erDuplicateIdentifier, Files^.PrevLine, Files^.PrevCol, '');
    ResName := LastLine;
    Consume( ctIdentifier);
    Consume( ctColon);
    if not ( LastToken in [ctIdentifier, ctString]) then
      Error( erTypeIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
    OpSym^.Definition^.ResType := ReadTypeDefinition( nil, SymbolTable);
    Consume( ctSemicolon);

    New(FuncStack);
    FuncStack^.Next := CurrentFunction;
    FuncStack^.Func := OpSym;
    CurrentFunction := FuncStack;

    case pFunctionSymbol(OpSym)^.Definition^.ResType^.DefType of
      cOrdDefinition,
      cUserOrdDefinition,
      cBooleanDefinition,
      cPointerDefinition:
        begin
          Sym := New( pVariableSymbol, Init( ResName, OpSym^.Definition^.ResType, cvtLocal, 0));
          Inc( OpSym^.Definition^.LocalSymbols^.DataSize,
            pVariableSymbol(Sym)^.Definition^.GetSize{$IFDEF PPRO}(){$ENDIF});
          pVariableSymbol(Sym)^.Offset := - OpSym^.Definition^.LocalSymbols^.DataSize;
          OpSym^.Definition^.LocalSymbols^.Insert( Sym);

          Sym := New( pVariableSymbol, Init( FuncResultName, OpSym^.Definition^.ResType, cvtLocal, 0));
          pVariableSymbol(Sym)^.Offset := - OpSym^.Definition^.LocalSymbols^.DataSize;
          OpSym^.Definition^.LocalSymbols^.Insert( Sym);
        end;
      cRealDefinition:
        begin
          Sym := New( pVariableSymbol, Init( ResName, OpSym^.Definition^.ResType, cvtLocal, 0));
          Inc( OpSym^.Definition^.LocalSymbols^.DataSize,
            pVariableSymbol(Sym)^.Definition^.GetSize{$IFDEF PPRO}(){$ENDIF});
          pVariableSymbol(Sym)^.Offset := - OpSym^.Definition^.LocalSymbols^.DataSize;
          OpSym^.Definition^.LocalSymbols^.Insert( Sym);

          Sym := New( pVariableSymbol, Init( FuncResultName, OpSym^.Definition^.ResType, cvtLocal, 0));
          pVariableSymbol( Sym)^.Offset := - OpSym^.Definition^.LocalSymbols^.DataSize;
          OpSym^.Definition^.LocalSymbols^.Insert( Sym);
        end;
      else
        begin
          Sym := New( pVariableSymbol, Init( ResName, OpSym^.Definition^.ResType, cvtVarParam, 0));
          pVariableSymbol(Sym)^.Offset := OpSym^.Definition^.ParamSize + 8;
          OpSym^.Definition^.LocalSymbols^.Insert( Sym);

          Sym := New( pVariableSymbol, Init( FuncResultName, OpSym^.Definition^.ResType, cvtVarParam, 0));
          pVariableSymbol(Sym)^.Offset := OpSym^.Definition^.ParamSize + 8;
          {Size := pVariableSymbol(Sym)^.Definition^.GetSize;
          if Size and 3 <> 0 then
            Size := Size and not 3 + 4;}
          Inc( OpSym^.Definition^.ParamSize, 4);
          OpSym^.Definition^.LocalSymbols^.Insert( Sym);
        end;
    end;

    Sym := SymbolTable^.Search( OpSym^.SymbolName^);
    if not Assigned( Sym) then
      SymbolTable^.Insert( OpSym)
    else
      begin
        if Sym^._Type <> cOperatorSymbol then
          Error( erDuplicateIdentifier, Files^.PrevLine, Files^.PrevCol, OpSym^.SymbolName^)
        else
          begin
            while Assigned( pFunctionSymbol(Sym)^.NextOverloaded) do
              begin
                if IsSameParams( pFunctionSymbol(Sym)^.Definition^.ParamColl,
                  OpSym^.Definition^.ParamColl) then
                    break;
                Sym := pFunctionSymbol(Sym)^.NextOverloaded;
              end;
            OpSym^.NextOverloaded := nil;
            if IsSameParams( pFunctionSymbol(Sym)^.Definition^.ParamColl,
              OpSym^.Definition^.ParamColl) then
                if Assigned( pFunctionSymbol(Sym)^.Definition^.Code) or
                ( pFunctionSymbol(Sym)^.Definition^.ResType <> OpSym^.Definition^.ResType) then
                  Error( erOverloadedFunctionWithSamesParameters, Files^.PrevLine, Files^.PrevCol, OpSym^.SymbolName^)
                else if not EqualHeaders( OpSym, pFunctionSymbol( Sym) ) then
                  Error( erHeaderDoesNotMatchPreviousDefinition,
                    Files^.PrevLine,  Files^ .PrevCol, OpSym^.SymbolName^)
                else
                  begin
                    Dispose( OpSym, Done{$IFDEF PPRO}(){$ENDIF});
                    OpSym := pOperatorSymbol(Sym);
                    CurrentFunction^.Func := OpSym;
                  end
            else
              begin
                pFunctionSymbol(Sym)^.NextOverloaded := OpSym;
                SymbolTable^.Insert( OpSym);
                {OpSym^.Owner := Sym^.Owner;}
              end;
          end;
      end;

    PushTable( OpSym^.Definition);
    if not OnlyHeader then
      begin
        while True do
          begin
            case LastToken of
              ctFORWARD:
                begin
                  Consume( ctFORWARD);
                  break;
                end;
              ctASSEMBLER:
                begin
                  if OpSym^.Definition^.CallType = cctDefault then
                    OpSym^.Definition^.SetCallType( cctPascal);
                  OpSym^.Definition^.ProcOptions :=
                    OpSym^.Definition^.ProcOptions or poAssembler;
                  Consume( ctAssembler);
                  Consume( ctSemicolon);
                  Result := pVariableSymbol(
                    OpSym^.Definition^.LocalSymbols^.FindSymbol( FuncResultName));
                  if Result^.Offset < 0 then
                    begin
                      if Result^.Definition^.GetSize{$IFDEF PPRO}(){$ENDIF} <= 4 then
                        Dec( OpSym^.Definition^.LocalSymbols^.DataSize, 4)
                      else
                        Dec( OpSym^.Definition^.LocalSymbols^.DataSize,
                          Result^.Definition^.GetSize{$IFDEF PPRO}(){$ENDIF});
                      Result^.Offset := 0;
                      Result^.IsRegisterable := True;
                      if Result^.Definition^.DefType = cRealDefinition then
                        Result^.Register := crST
                      else
                        Result^.Register := crEAX;

                      Result := pVariableSymbol(
                        OpSym^.Definition^.LocalSymbols^.FindSymbol( ResName));
                      Result^.Offset := 0;
                      Result^.IsRegisterable := True;
                      if Result^.Definition^.DefType = cRealDefinition then
                        Result^.Register := crST
                      else
                        Result^.Register := crEAX;
                    end;
                end;
              else
                begin
                  if OpSym^.Definition^.CallType = cctDefault then
                    OpSym^.Definition^.SetCallType( cctPascal);
                  ReadProcedureDefinition( OpSym^.Definition^.LocalSymbols);
                  break;
                end;
            end;
          end;
        Consume( ctSemicolon);
      end;

    Dec( CurLevel);
    PopTable{$IFDEF PPRO}(){$ENDIF};
    FuncStack := CurrentFunction;
    CurrentFunction := CurrentFunction^.Next;
    Dispose( FuncStack);
  end;

function tCompiler.ReadExpression( ResType: pDefinition): pCodeTree;

  function MulNode( ResType: pDefinition): pCodeTree;
    var
      Code, CodeTree: pCodeTree;
    begin
      CodeTree := GetCodeNode( ResType);
      while True do
        begin
          case LastToken of
            ctStar:
              begin
                Code := New( pCodeTree, CreateMultiplication( nil, nil, nil, Files^.PrevLine, Files^.PrevCol));
                Consume( ctStar);
              end;
            ctDiv:
              begin
                Code := New( pCodeTree, CreateDiv( nil, nil, nil, Files^.PrevLine, Files^.PrevCol));
                Consume( ctDiv);
              end;
            ctSlash:
              begin
                Code := New( pCodeTree, CreateDivision( nil, nil, nil, Files^.PrevLine, Files^.PrevCol));
                Consume( ctSlash);
              end;
            ctMod:
              begin
                Code := New( pCodeTree, CreateMod( nil, nil, nil, Files^.PrevLine, Files^.PrevCol));
                Consume( ctMod);
              end;
            ctAnd:
              begin
                Code := New( pCodeTree, CreateAnd( nil, Files^.PrevLine, Files^.PrevCol));
                Consume( ctAnd);
              end;
            ctShl:
              begin
                Code := New( pCodeTree, CreateShl( nil, Files^.PrevLine, Files^.PrevCol));
                Consume( ctShl);
              end;
            ctShr:
              begin
                Code := New( pCodeTree, CreateShr( nil, Files^.PrevLine, Files^.PrevCol));
                Consume( ctShr);
              end;
            else
              break;
          end;
          Code^.Left := CodeTree;
          Code^.Right := GetCodeNode( ResType);
          CodeTree := Code;
        end;
      MulNode := CodeTree;
    end;

  function AddNode( ResType: pDefinition): pCodeTree;
    var
      Code, CodeTree: pCodeTree;
    begin
      CodeTree := MulNode( ResType);
      while True do
        begin
          case LastToken of
            ctPlus:
              begin
                Code := New( pCodeTree, CreateAddition( nil, nil, nil, Files^.PrevLine, Files^.PrevCol));
                Consume( ctPlus);
              end;
            ctMinus:
              begin
                Code := New( pCodeTree, CreateSubtraction( nil, nil, nil, Files^.PrevLine, Files^.PrevCol));
                Consume( ctMinus);
              end;
            ctOr:
              begin
                Code := New( pCodeTree, CreateOr( nil, Files^.PrevLine, Files^.PrevCol));
                Consume( ctOr);
              end;
            ctXor:
              begin
                Code := New( pCodeTree, CreateXor( nil, Files^.PrevLine, Files^.PrevCol));
                Consume( ctXor);
              end;
            else
              break;
          end;
          Code^.Left := CodeTree;
          Code^.Right := MulNode( ResType);
          CodeTree := Code;
        end;
      AddNode := CodeTree;
    end;

  function CompareNode( ResType: pDefinition): pCodeTree;
    var
      CodeTree, Code: pCodeTree;
    begin
      CodeTree := AddNode( ResType);
      while True do
        begin
          case LastToken of
            ctEqual:
              begin
                Code := New( pCodeTree, CreateEqual( nil, Files^.PrevLine, Files^.PrevCol));
                Consume( ctEqual);
              end;
            ctUnequal:
              begin
                Code := New( pCodeTree, CreateUnequal( nil, Files^.PrevLine, Files^.PrevCol));
                Consume( ctUnequal);
              end;
            ctGreater:
              begin
                Code := New( pCodeTree, CreateGreater( nil, Files^.PrevLine, Files^.PrevCol));
                Consume( ctGreater);
              end;
            ctLess:
              begin
                Code := New( pCodeTree, CreateLess( nil, Files^.PrevLine, Files^.PrevCol));
                Consume( ctLess);
              end;
            ctGreaterEq:
              begin
                Code := New( pCodeTree, CreateGreaterEq( nil, Files^.PrevLine, Files^.PrevCol));
                Consume( ctGreaterEq);
              end;
            ctLessEq:
              begin
                Code := New( pCodeTree, CreateLessEq( nil, Files^.PrevLine, Files^.PrevCol));
                Consume( ctLessEq);
              end;
            ctIN:
              begin
                Code := New( pCodeTree, CreateIN( nil, Files^.PrevLine, Files^.PrevCol));
                Consume( ctIN);
              end;
            else
              break;
          end;
          Code^.Left := CodeTree;
          Code^.Right := AddNode( ResType);
          CodeTree := Code;
        end;
      CompareNode := CodeTree;
    end;

  function AssignNode( ResType: pDefinition): pCodeTree;
    var
      CodeTree, Code: pCodeTree;
      AsnType: tCodeType;
    begin
      CodeTree := CompareNode( ResType);
      case LastToken of
        ctAssignment:
              begin
                AsnType := cctAssignment;
                Consume( ctAssignment);
              end;
        ctPlusAsn:
              begin
                AsnType := cctPlusAsn;
                Consume( ctPlusAsn);
              end;
        ctMinusAsn:
          begin
            AsnType := cctMinusAsn;
            Consume( ctMinusAsn);
          end;
        ctAndAsn:
          begin
            AsnType := cctAndAsn;
            Consume( ctAndAsn);
          end;
        ctOrAsn:
          begin
            AsnType := cctOrAsn;
            Consume( ctOrAsn);
          end;
        ctStarAsn:
          begin
            AsnType := cctStarAsn;
            Consume( ctStarAsn);
          end;
        ctSlashAsn:
          begin
            AsnType := cctSlashAsn;
            Consume( ctSlashAsn);
          end;
        ctDivAsn:
          begin
            AsnType := cctDivAsn;
            Consume( ctDivAsn);
          end;
        ctModAsn:
          begin
            AsnType := cctModAsn;
            Consume( ctModAsn);
          end;
        ctShlAsn:
          begin
            AsnType := cctShlAsn;
            Consume( ctShlAsn);
          end;
        ctShrAsn:
          begin
            AsnType := cctShrAsn;
            Consume( ctShrAsn);
          end;
        ctXorAsn:
          begin
            AsnType := cctXorAsn;
            Consume( ctXorAsn);
          end;
        else
          begin
            AssignNode := CodeTree;
            Exit;
          end;
      end;
      if (GetParamType( CodeTree) <> cvtVarParam) or
        (CodeTree^.Node.CodeType = cctAssignment) then
        if not (CodeTree^.Node.CodeType in [cctMem, cctPort]) then
          Error( erErrorInStatement, Files^.PrevLine, Files^.PrevCol, '');
      if not Assigned( CodeTree) then
        Error( erInternalError, Files^.CurLine, Files^.CurCol, '');
      Code := New( pCodeTree, CreateAssignment( AsnType, CodeTree^.ResType, nil, nil, Files^.PrevLine, Files^.PrevCol));
      Code^.Left := CodeTree;
      Code^.Right := ReadExpression( CodeTree^.ResType);
      CodeTree := Code;
      AssignNode := CodeTree;
    end;

  var
      CodeTree: pCodeTree;
      Line, Col: LongInt;
  begin
    Line := Files^.PrevLine;
    Col := Files^.PrevCol;
    CodeTree := AssignNode( ResType);
    OptomizeExpression( CodeTree);
    if Assigned( ResType) and Assigned( CodeTree^.ResType) then
      if (ResType^.DefType = cArrayDefinition) and
        (CodeTree^.Node.CodeType = cctStringConst) then
        MakeTypeConversion( CodeTree, ResType)
      else
        if not CompatibleTypes( ResType, CodeTree^.ResType) then
          Error( erTypeMismatch, Files^.PrevLine, Files^.PrevCol, '');
    CodeTree^.Line := Line;
    CodeTree^.Col := Col;
    ReadExpression := CodeTree;
  end;

procedure tCompiler.ReadStatement( var StatementCode: pCodeTree);
  var
    _Code: pCodeTree;
    CurCode: pCodeTree;
    CodeTree: pCodeTree;
    Symbol: pSymbol;
    Level: LongInt;
  begin
    case LastToken of
      ctSemicolon:;
        {Consume(ctSemicolon);}

      ctBEGIN:
        begin
          Consume(ctBegin);
          _Code := nil;
          while LastToken <> ctEND do
            begin
              while LastToken = ctSemicolon do
                Consume( ctSemicolon);
              if LastToken = ctEND then break;
              if Assigned( _Code) then
                begin
                  while Assigned( CurCode^.Left) do CurCode := CurCode^.Left;
                  ReadStatement( CurCode^.Left);
                end
              else
                begin
                  ReadStatement( _Code);
                  CurCode := _Code;
                end;
              CodeTree := CurCode;
              if Assigned( CodeTree) then
                while Assigned( CodeTree^.Left) do
                  CodeTree := CodeTree^.Left;
              if (LastToken <> ctEND) and
                not (Assigned( CodeTree) and (CodeTree^.Node.CodeType = cctLabel)) then
                Consume( ctSemicolon);
            end;
          Consume(ctEND);
          if not (LastToken in [ctSemiColon, ctEnd, ctPoint, ctELSE]) then
            Error( erSemicolonExpected, Files^.PrevLine, Files^.PrevCol, '');
          CurCode := New( pCodeTree, CreateBlock( _Code, Files^.PrevLine, Files^.PrevCol));
          StatementCode := CurCode;
        end;

      ctIdentifier,
      ctNew,
      ctDispose,
      ctInherited:
        begin
          Symbol := CurrentFunction^.Func^.Definition^.LocalSymbols^.Search( LastLine);
          if not Assigned( Symbol) or (Symbol^._Type <> cLabelSymbol) then
            begin
              _Code := ReadExpression( nil);
              if not (_Code^.Node.CodeType in
                [ cctAssignment, cctFunctionCall, cctExpression, cctInc, cctDec,
                  cctBlock, cctAssign, cctWrite, cctWriteLn, cctRead, cctReadLn,
                  cctNew, cctDispose, cctInclude, cctExclude]) then
                begin
                  Error( erErrorInStatement, Files^.PrevLine, Files^.PrevCol, '');
                  Dispose( _Code, Done);
                end
              else
                begin
                  if not (_Code^.Node.CodeType in
                    [cctBlock, cctExpression]) then
                    _Code := New( pCodeTree, CreateExpression( _Code, nil, Files^.PrevLine, Files^.PrevCol));
                  StatementCode := _Code;
                end;
            end
          else
            begin
              if pLabelSymbol( Symbol)^.IsAssigned then
                Error( erLabelAlreadyDefined, Files^.PrevLine, Files^.PrevCol, LastLine);
              StatementCode := New( pCodeTree, CreateLabel(
                pLabelSymbol( Symbol),
                Files^.PrevLine, Files^.PrevCol));
              pLabelSymbol( Symbol)^.IsAssigned := True;
              Consume( ctIdentifier);
              Consume( ctColon);
            end;
        end;
      ctASM:
        begin
          StatementCode := ReadAsmStatement{$IFDEF PPRO}(){$ENDIF};
        end;
      ctIF:
        StatementCode := ReadIfStatement{$IFDEF PPRO}(){$ENDIF};
      ctWHILE:
        StatementCode := ReadWHILEStatement{$IFDEF PPRO}(){$ENDIF};
      ctRepeat:
        StatementCode := ReadRepeatUntilStatement{$IFDEF PPRO}(){$ENDIF};
      ctFOR:
        StatementCode := ReadForStatement{$IFDEF PPRO}(){$ENDIF};
      ctCASE:
        StatementCode := ReadCaseStatement{$IFDEF PPRO}(){$ENDIF};
      ctBREAK:
        begin
          Consume( ctBREAK);
          if LoopLevel > 0 then
            StatementCode := New( pCodeTree, CreateBreak{$IFDEF PPRO}(){$ENDIF})
          else
            Error( erNoEnclosingCycleStatement, Files^.PrevLine, Files^.PrevCol, '');
        end;
      ctCONTINUE:
        begin
          Consume( ctCONTINUE);
          if LoopLevel > 0 then
            StatementCode := New( pCodeTree, CreateContinue{$IFDEF PPRO}(){$ENDIF})
          else
            Error( erNoEnclosingCycleStatement, Files^.PrevLine, Files^.PrevCol, '');
        end;
      ctEXIT:
        begin
          Consume( ctEXIT);
          StatementCode := New( pCodeTree, CreateExit{$IFDEF PPRO}(){$ENDIF});
        end;
      ctWITH:
        begin
          Consume( ctWITH);
          StatementCode := ReadWithStatement;
        end;
      ctGOTO:
        begin
          if NextToken <> ctIdentifier then
            Error( erLabelIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
          Symbol := FindSymbol( LastLine, Level);
          if Symbol^._Type <> cLabelSymbol then
            Error( erLabelIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
          if CurLevel <> GetLexLevel( Symbol) then
            Error( erLabelNotWithinCurrentBlock, Files^.PrevLine, Files^.PrevCol, LastLine);
          StatementCode := New( pCodeTree, CreateGOTO( pLabelSymbol( Symbol),
            Files^.PrevLine, Files^.PrevCol));
          Consume( ctIdentifier);
        end;
      else
        Error( erErrorInStatement, Files^.PrevLine, Files^.PrevCol, '');
    end;
  end;

procedure tCompiler.ReadProcedureDefinition(LocalSymbols: pSymbolTable);

  procedure CheckLabels( Symbol: pLabelSymbol); {$IFDEF TP}far;{$ENDIF}
    begin
      if Assigned( Symbol) and (Symbol^._Type = cLabelSymbol) and
        not Symbol^.IsAssigned then
        Error( erUndefinedLabelInPrecedingStatement,
          Files^.PrevLine, Files^.PrevCol,
          Symbol^.SymbolName^);
    end;

  var
    CodeTree: pCodeTree;
    VarType: tVariableType;
  begin
    if LocalSymbols^.SymbolTableType = stGlobalTable then
      VarType := cvtGlobal
    else
      VarType := cvtLocal;
    while True do
      begin
        case LastToken of
          ctLabel:
            ReadLabels( LocalSymbols);
          ctConst:
            ReadConsts( LocalSymbols);
          ctType:
            ReadTypes( LocalSymbols);
          ctVar:
            begin
              Consume( ctVar);
              Inc( LocalSymbols^.DataSize, ReadVariables( LocalSymbols, VarType, LocalSymbols^.DataSize));
              {Consume( ctSemicolon);}
            end;
          ctProcedure,
          ctFunction,
          ctConstructor,
          ctDestructor:
            ReadProcedure( LocalSymbols, nil, False);
          ctOperator:
            ReadOperator( LocalSymbols, False);
          else
            break;
        end;
        {LastToken := GetLexeme;}
      end;

    if CurrentFunction^.Func^.Definition^.ProcOptions and poAssembler <> 0 then
      begin
        if LastToken <> ctASM then
          Error( erASMExpected, Files^.PrevLine, Files^.PrevCol, '');
        CurrentFunction^.Func^.Definition^.Code :=
          ReadAsmStatement{$IFDEF PPRO}(){$ENDIF};
      end
    else
      if LastToken = ctBegin then
        begin
          CodeTree := nil;
          ReadStatement( CodeTree);
          CurrentFunction^.Func^.Definition^.Code := CodeTree;
        end
      else
        Error(erBEGINExpected, Files^.PrevLine, Files^.PrevCol, '');
    LocalSymbols^.ForEach( @CheckLabels);
  end;


function tCompiler.ReadFunctionType( SymbolTable: pSymbolTable): pDefinition;
  var
    ReadResultType: Boolean;
    TypeDef: pFunctionTypeDefinition;
  begin
    ReadResultType := LastToken = ctFunction;
    TypeDef := New( pFunctionTypeDefinition, Init( nil));
    ReadFunctionParameters( TypeDef, 255, SymbolTable);
    if ReadResultType then
      begin
        Consume( ctColon);
        if not ( LastToken in [ctIdentifier, ctString]) then
          Error( erTypeIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
        TypeDef^.ResType := ReadTypeDefinition( nil, SymbolTable);
        if not (TypeDef^.ResType^.DefType in [ cOrdDefinition, cUserOrdDefinition,
          cBooleanDefinition, cPointerDefinition, cRealDefinition]) then
          Inc( TypeDef^.ParamSize, 4);
      end;
    while True do
      begin
        case LastToken of
          ctSTDCALL:
            begin
              TypeDef^.CallType := cctSTDCALL;
              Consume( ctSTDCALL);
            end;
          ctPASCAL:
            begin
              TypeDef^.CallType := cctPASCAL;
              Consume( ctPASCAL);
            end;
          ctCDECL:
            begin
              TypeDef^.CallType := cctCDECL;
              Consume( ctCDECL);
            end;
        else
          break;
        end;
        Consume( ctSemicolon);
      end;
    if TypeDef^.CallType = cctDefault then
      TypeDef^.CallType :=  cctPascal;
    ReadFunctionType := TypeDef;
  end;

function tCompiler.ReadTypeDefinition( TypeSymbol: pTypeSymbol; SymbolTable: pSymbolTable): pDefinition;
  var
    Expr: pCodeTree;
    Min, Max, Line, Col, L: LongInt;
    Symbol: pSymbol;
    Def, TypeDef: pDefinition;
    Symbols: pSymbolTable;
    OldSymOptions: LongInt;
  begin
    TypeDef := nil;
      case LastToken of
        ctIdentifier:
          begin
            Symbol := FindSymbol( LastLine, L);
            if not Assigned( Symbol) then
              Error( erUnknownIdentifier, Files^.PrevLine, Files^.PrevCol, LastLine);
            case Symbol^._Type of
              cConstSymbol:
                begin
                  Line := Files^.PrevLine;
                  Col := Files^.PrevCol;
                  Expr := ReadExpression( LongDef);
                  if not IsConst( Expr) then
                    Error( erCannotEvaluateThisExpression, Line, Col, '');
                  if Expr^.Node.CodeType <> cctIntConst then
                    Error( erInvalidSubrangeBaseType, Line, Col, '');
                  Min := Expr^.Node.IntValue;
                  Dispose( Expr, Done);
                  Consume( ctPointPoint);
                  Line := Files^.PrevLine;
                  Col := Files^.PrevCol;
                  Expr := ReadExpression( LongDef);
                  if not IsConst( Expr) then
                    Error( erCannotEvaluateThisExpression, Line, Col, '');
                  if Expr^.Node.CodeType <> cctIntConst then
                    Error( erInvalidSubrangeBaseType, Line, Col, '');
                  Max := Expr^.Node.IntValue;
                  Dispose( Expr, Done);
                  if Max < Min then
                    Error( erLowerBoundGreaterThanUpperBound, Line, Col, '');
                  TypeDef := New( pOrdDefinition, Init( GetBaseType(Min, Max), Min, Max));
                end;
              cTypeSymbol:
                begin
                  Consume( ctIdentifier);
                  TypeDef := pTypeSymbol(Symbol)^.Definition;
                end;
              cUnitSymbol:
                begin
                  Consume( ctIdentifier);
                  Consume( ctPoint);
                  if LastToken <> ctIdentifier then
                    Error( erTypeIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
                  Symbol := pUnitSymbol( Symbol)^.UnitSymbols^.FindSymbol( LastLine);
                  if not Assigned( Symbol) then
                    Error( erUnknownIdentifier, Files^.PrevLine, Files^.PrevCol, '');
                  if Symbol^._Type <> cTypeSymbol then
                    Error( erTypeIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
                  Consume( ctIdentifier);
                  TypeDef := pTypeSymbol( Symbol)^.Definition;
                end;
              cSystemSymbol:
                begin
                  Line := Files^.PrevLine;
                  Col := Files^.PrevCol;
                  Expr := ReadExpression( LongDef);
                  if not IsConst( Expr) then
                    Error( erCannotEvaluateThisExpression, Line, Col, '');
                  if Expr^.Node.CodeType <> cctIntConst then
                    Error( erInvalidSubrangeBaseType, Line, Col, '');
                  Min := Expr^.Node.IntValue;
                  Dispose( Expr, Done{$IFDEF PPRO}(){$ENDIF});
                  Consume( ctPointPoint);
                  Line := Files^.PrevLine;
                  Col := Files^.PrevCol;
                  Expr := ReadExpression( LongDef);
                  if not IsConst( Expr) then
                    Error( erCannotEvaluateThisExpression, Line, Col, '');
                  if Expr^.Node.CodeType <> cctIntConst then
                    Error( erInvalidSubrangeBaseType, Line, Col, '');
                  Max := Expr^.Node.IntValue;
                  Dispose( Expr, Done{$IFDEF PPRO}(){$ENDIF});
                  if Max < Min then
                    Error( erLowerBoundGreaterThanUpperBound, Line, Col, '');
                  TypeDef := New( pOrdDefinition, Init( GetBaseType(Min, Max), Min, Max));
                end;
            end;
          end;
        ctLParen:
          begin
            {consume( ctLParen);}
            TypeDef := New( pUserOrdDefinition, Init{$IFDEF PPRO}(){$ENDIF});
            Max := -1;
            repeat
              Inc( Max);
              if NextToken{$IFDEF PPRO}(){$ENDIF} <> ctIdentifier then
                Error( erIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
              Symbol := FindLocalSymbol( LastLine);
              if Assigned( Symbol) then
                Error( erDuplicateIdentifier, Files^.PrevLine, Files^.PrevCol, LastLine);
              SymbolTable^.Insert( New( pUserOrdSymbol, Init( LastLine, Max, pUserOrdDefinition(TypeDef), SymbolsOptions )));
            until NextToken{$IFDEF PPRO}(){$ENDIF} <> ctComma;
            pUserOrdDefinition( TypeDef)^.Max := Max;
            if LastToken <> ctRParen then
              Error( erRightParenExpected, Files^.PrevLine, Files^.PrevCol, '');
            NextToken{$IFDEF PPRO}(){$ENDIF};
          end;

        ctMinus,
        ctPlus,
        ctIntConst:
          begin
            Line := Files^.PrevLine;
            Col := Files^.PrevCol;
            Expr := ReadExpression( LongDef);
            if not IsConst( Expr) then
              Error( erCannotEvaluateThisExpression, Line, Col, '');
            if Expr^.Node.CodeType <> cctIntConst then
              Error( erInvalidSubrangeBaseType, Line, Col, '');
            Min := Expr^.Node.IntValue;
            Dispose( Expr, Done{$IFDEF PPRO}(){$ENDIF});
            Consume( ctPointPoint);
            Line := Files^.PrevLine;
            Col := Files^.PrevCol;
            Expr := ReadExpression( LongDef);
            if not IsConst( Expr) then
              Error( erCannotEvaluateThisExpression, Line, Col, '');
            if Expr^.Node.CodeType <> cctIntConst then
              Error( erInvalidSubrangeBaseType, Line, Col, '');
            Max := Expr^.Node.IntValue;
            Dispose( Expr, Done{$IFDEF PPRO}(){$ENDIF});
            if Max < Min then
              Error( erLowerBoundGreaterThanUpperBound, Line, Col, '');
            TypeDef := New( pOrdDefinition, Init( GetBaseType(Min, Max), Min, Max));
          end;

        ctCharConst:
          begin
            Line := Files^.PrevLine;
            Col := Files^.PrevCol;
            Expr := ReadExpression( CharDef);
            if not IsConst( Expr) then
              Error( erCannotEvaluateThisExpression, Line, Col, '');
            if Expr^.Node.CodeType <> cctCharConst then
              Error( erInvalidSubrangeBaseType, Line, Col, '');
            Min := Byte(Expr^.Node.CharValue);
            Dispose( Expr, Done);
            Consume( ctPointPoint);
            Line := Files^.PrevLine;
            Col := Files^.PrevCol;
            Expr := ReadExpression( CharDef);
            if not IsConst( Expr) then
              Error( erCannotEvaluateThisExpression, Line, Col, '');
            if Expr^.Node.CodeType <> cctCharConst then
              Error( erInvalidSubrangeBaseType, Line, Col, '');
            Max := Byte(Expr^.Node.CharValue);
            Dispose( Expr, Done{$IFDEF PPRO}(){$ENDIF});
            if Max < Min then
              Error( erLowerBoundGreaterThanUpperBound, Line, Col, '');
            TypeDef := New( pOrdDefinition, Init( cbtChar, Min, Max));
          end;
        ctString:
          begin
            if NextToken = ctLBracket then
              begin
                Consume( ctLBracket);
                Line := Files^.PrevLine;
                Col := Files^.PrevCol;
                Expr := ReadExpression( LongDef);
                if not IsConst( Expr) then
                  Error( erCannotEvaluateThisExpression, Line, Col, '');
                if Expr^.Node.CodeType <> cctIntConst then
                  Error( erIntegerConstantExpected, Line, Col, '');
                Max := Expr^.Node.IntValue;
                Dispose( Expr, Done);
                Consume( ctRBracket);
                TypeDef := New( pStringDefinition, Init( Max));
              end
            else
              TypeDef := StringDef;
          end;

        ctFunction,
        ctProcedure:
          TypeDef := ReadFunctionType( SymbolTable);

        ctFile:
          begin
            Consume( ctFILE);
            if LastToken <> ctOF then
              TypeDef := UntypedFileDef
            else
              begin
                Consume( ctOF);
                Def := ReadTypeDefinition( nil, SymbolTable);
                TypeDef := New( pFileDefinition, Init( cftTyped, Def));
              end;
          end;

        ctArray:
          begin
            Consume( ctArray);
            if LastToken <> ctLBracket then
              Error( erLeftBracketExpected, Files^.PrevLine, Files^.PrevCol, '');
            TypeDef := New( pArrayDefinition, Init( nil, nil));
            Def := TypeDef;
            repeat
              NextToken{$IFDEF PPRO}(){$ENDIF};
              pArrayDefinition(Def)^.IndexDef :=
                ReadTypeDefinition( nil, SymbolTable);
              if LastToken = ctComma then
                begin
                  pArrayDefinition(Def)^.ComponentDef :=
                    New( pArrayDefinition, Init( nil, nil));
                  Def := pArrayDefinition(Def)^.ComponentDef;
                end;
            until LastToken <> ctComma;
            Consume( ctRBracket);
            Consume( ctOF);
            pArrayDefinition(Def)^.ComponentDef :=
              ReadTypeDefinition( nil, SymbolTable);
          end;
        ctSet:
          begin
            Consume( ctSET);
            Consume( ctOF);
            Def := ReadTypeDefinition( nil, SymbolTable);
            if not Assigned( Def) or
              not (Def^.DefType in [ cOrdDefinition, cBooleanDefinition, cUserOrdDefinition]) then
              Error( erOrdinalTypeExpected, Files^.PrevLine, Files^.PrevCol, '');
            TypeDef := New( pSetDefinition, Init( Def));
          end;

        ctRecord:
          begin
            Symbols := New( pSymbolTable, Init( stRecordTable, 0, 1));
            Consume( ctRecord);
            OldSymOptions := SymbolsOptions;
            SymbolsOptions := csoPublicSymbol;
            if LastToken = ctIdentifier then
              Inc(Symbols^.DataSize, ReadVariables( Symbols, cvtField, 0));
            {else
              Error( erErrorInType, Files^.PrevLine, Files^.PrevCol, '');}
            TypeDef := New( pRecordDefinition, Init( Symbols));
            if LastToken = ctCase then
              Inc( Symbols^.DataSize, ReadCaseRecord( Symbols));
            SymbolsOptions := OldSymOptions;
            Consume( ctEnd);
          end;

        ctObject:
          begin
            Consume( ctObject);
            TypeDef := ReadObjectDefinition( TypeSymbol, SymbolTable);
          end;

        ctCarret:
          begin
            if NextToken{$IFDEF PPRO}(){$ENDIF} <> ctIdentifier then
              if LastToken <> ctString then
                Error( erTypeIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '')
              else
                begin
                  TypeDef := New( pPointerDefinition, Init( StringDef));
                  NextToken{$IFDEF PPRO}(){$ENDIF};
                end
            else
              begin
                Symbol := FindLocalSymbol( LastLine);
                if Assigned( Symbol) then
                  begin
                    if Symbol^._Type <> cTypeSymbol then
                      begin
                        Error( erTypeIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
                        ReadTypeDefinition := nil;
                        Exit;
                      end;
                  end
                else
                  Symbol := FindSymbol( LastLine, L);
                if Assigned( Symbol) and (Symbol^._Type = cTypeSymbol) then
                  begin
                    TypeDef := New( pPointerDefinition, Init(
                      pTypeSymbol( Symbol)^.Definition));
                  end
                else
                  begin
                    Symbol := New( pTypeSymbol, Init( LastLine, nil, SymbolsOptions));
                    TypeDef := New( pPointerDefinition, Init( nil));
                    TypeDef^.Line := Files^.PrevLine;
                    TypeDef^.Col := Files^.PrevCol;
                    SymbolTable^.Insert( Symbol);
                  end;
                pPointerDefinition(TypeDef)^.DefSym := Symbol;
                NextToken;
              end;
          end;
        else
          Error( erErrorInType, Files^.PrevLine, Files^.PrevCol, '');
      end;
    ReadTypeDefinition := TypeDef;
  end;

procedure tCompiler.CreateSystemTypes;
  var
    OldSwitches: tSwitches;
  begin
    if csCompileSystem in Switches then
      begin
        CharDef := New( pOrdDefinition, Init( cbtChar, 0, 255));
        ShortDef := New( pOrdDefinition, Init(cbtShortInt, -128, 127));
        ByteDef := New( pOrdDefinition, Init( cbtByte, 0, 255));
        IntDef := New( pOrdDefinition, Init( cbtInteger, -32768, 32767));
        WordDef := New( pOrdDefinition, Init( cbtWord, 0, 65535));
        LongDef := New( pOrdDefinition, Init( cbtLongInt, $80000000, $7fffffff));
        DWordDef := New( pOrdDefinition, Init( cbtDWord, 0, $FFFFFFFF));
        ExtendedDef := New( pRealDefinition, Init( crtExtended));
        StringDef := New( pStringDefinition, Init( 255));
        BoolDef := New( pBooleanDefinition, Init( cbBoolean));
        VoidDef := New( pDefinition, Init);
        PointerDef := New( pPointerDefinition, Init( VoidDef));
        UntypedFileDef := New( pFileDefinition, Init( cftUntyped, nil));
      end
    else
      begin
        OldSwitches := DefaultSwitches;
        DefaultSwitches := DefaultSwitches + [csCompileSystem];
        LoadUnit( 'SYSTEM');
        ReadSystemTypes;
        DefaultSwitches := OldSwitches;
      end;
  end;

function FindDefinition( const aName: tNameString;
  SymbolTable: pSymbolTable): pDefinition;
  var
    Sym: pTypeSymbol;
  begin
    FindDefinition := nil;
    if Assigned( SymbolTable) then
      begin
        Sym := pTypeSymbol( SymbolTable^.FindSymbol( aName));
        if Assigned( Sym) and (Sym^._Type = cTypeSymbol) then
          FindDefinition := Sym^.Definition;
      end;
  end;

procedure tCompiler.ReadSystemTypes;
  var
    SymbolTable: pSymbolTable;
    I: tIndex;
  begin
    if Assigned( UnitCollection) and
      UnitCollection^.Search( @SystemUnitName, I) then
        begin
          SymbolTable := pUnitItem( UnitCollection^.At( I))^.SymbolTable;
          CharDef := pOrdDefinition( FindDefinition( 'char', SymbolTable));
          ShortDef := pOrdDefinition( FindDefinition( 'shortint', SymbolTable));
          ByteDef := pOrdDefinition( FindDefinition( 'byte', SymbolTable));
          IntDef := pOrdDefinition( FindDefinition( 'integer', SymbolTable));
          WordDef := pOrdDefinition( FindDefinition( 'word', SymbolTable));
          LongDef := pOrdDefinition( FindDefinition( 'longint', SymbolTable));
          DWordDef := pOrdDefinition( FindDefinition( 'DWORD', SymbolTable));
          StringDef := pStringDefinition( FindDefinition( 'STRING', SymbolTable));
          BoolDef := pBooleanDefinition( FindDefinition( 'BOOLEAN', SymbolTable));
          ExtendedDef := pRealDefinition( FindDefinition( 'EXTENDED', SymbolTable));
          PointerDef := pPointerDefinition( FindDefinition( 'POINTER', SymbolTable));
          VoidDef := FindDefinition( 'void', SymbolTable);
          UntypedFileDef := pFileDefinition( FindDefinition( 'untypedfile', SymbolTable));
        end;
  end;

procedure tCompiler.CreateSystemSymbols;
  var
    Sym: pTypeSymbol;
  begin
    if (csCompileSystem in Switches) and
      Assigned(GlobalSymbols) then with GlobalSymbols^ do
      begin
        Insert( New( pTypeSymbol, Init( 'char', CharDef, csoPublicSymbol)));
        Insert( New( pTypeSymbol, Init( 'shortint', ShortDef, csoPublicSymbol)));
        Insert( New( pTypeSymbol, Init( 'byte', ByteDef, csoPublicSymbol)));
        Insert( New( pTypeSymbol, Init( 'integer', IntDef, csoPublicSymbol)));
        Insert( New( pTypeSymbol, Init( 'word', WordDef, csoPublicSymbol)));
        Insert( New( pTypeSymbol, Init( 'longint', LongDef, csoPublicSymbol)));
        Insert( New( pTypeSymbol, Init( 'DWORD', DWordDef, csoPublicSymbol)));

        Insert( New( pTypeSymbol, Init( 'STRING', StringDef, csoPublicSymbol)));

        Insert( New( pTypeSymbol, Init( 'BOOLEAN',  BoolDef, csoPublicSymbol)));
        Insert( New( pTypeSymbol, Init( 'WORDBOOL', New( pBooleanDefinition, Init( cbWordBool)), csoPublicSymbol )));
        Insert( New( pTypeSymbol, Init( 'LONGBOOL', New( pBooleanDefinition, Init( cbLongBool)), csoPublicSymbol )));

        Insert( New( pTypeSymbol, Init( 'SINGLE', New( pRealDefinition, Init( crtSingle)), csoPublicSymbol )));
        Insert( New( pTypeSymbol, Init( 'DOUBLE', New( pRealDefinition, Init( crtDouble)), csoPublicSymbol )));
        Insert( New( pTypeSymbol, Init( 'EXTENDED', ExtendedDef, csoPublicSymbol)));

        Insert( New( pTypeSymbol, Init( 'POINTER', PointerDef, csoPublicSymbol)));
        Sym := New( pTypeSymbol, Init( 'void', VoidDef, csoPublicSymbol));
        PointerDef^.DefSym := Sym;
        Insert( Sym);

        Sym := New( pTypeSymbol, Init( 'TEXT',  New( pFileDefinition, Init(
          cftTextFile, nil)), csoPublicSymbol));
        Insert( Sym);

        Insert( New( pTypeSymbol, Init( 'untypedfile', UntypedFileDef, csoPublicSymbol)));
        Insert( New( pTypeSymbol, Init( 'TYPEDFILE',
            New( pFileDefinition, Init( cftTyped, VoidDef)), csoPublicSymbol )));

        Insert( New( pVariableSymbol, Init( 'INPUT',
          pTypeSymbol( Sym)^.Definition, cvtGlobal, csoPublicSymbol)));

        Insert( New( pVariableSymbol, Init( 'OUTPUT',
          pTypeSymbol( Sym)^.Definition, cvtGlobal, csoPublicSymbol)));

        { Создание системных символов вроде Read, Write, New, Dispose, ... }
        Insert( New( pSystemSymbol, Init( 'WRITE', csstWrite, csoPublicSymbol)));
        Insert( New( pSystemSymbol, Init( 'WRITELN', csstWriteLn, csoPublicSymbol)));

        Insert( New( pSystemSymbol, Init( 'READ', csstRead, csoPublicSymbol)));
        Insert( New( pSystemSymbol, Init( 'READLN', csstReadLn, csoPublicSymbol)));

        Insert( New( pSystemSymbol, Init( 'SIZEOF', csstSizeOf, csoPublicSymbol)));

        Insert( New( pSystemSymbol, Init( 'STR', csstSTR, csoPublicSymbol)));

        Insert( New( pSystemSymbol, Init( 'CHR', csstCHR, csoPublicSymbol)));
        Insert( New( pSystemSymbol, Init( 'ORD', csstORD, csoPublicSymbol)));

        Insert( New( pSystemSymbol, Init( 'PRED', csstPRED, csoPublicSymbol)));
        Insert( New( pSystemSymbol, Init( 'SUCC', csstSUCC, csoPublicSymbol)));

        Insert( New( pSystemSymbol, Init( 'INC', csstINC, csoPublicSymbol)));
        Insert( New( pSystemSymbol, Init( 'DEC', csstDEC, csoPublicSymbol)));

        Insert( New( pSystemSymbol, Init( 'LENGTH', csstLength, csoPublicSymbol)));

        Insert( New( pSystemSymbol, Init( 'ASSIGN', csstAssign, csoPublicSymbol)));

        Insert( New( pSystemSymbol, Init( 'ABS', csstABS, csoPublicSymbol)));

        Insert( New( pSystemSymbol, Init( 'ODD', csstODD, csoPublicSymbol)));

        Insert( New( pSystemSymbol, Init( 'SIN', csstSin, csoPublicSymbol)));
        Insert( New( pSystemSymbol, Init( 'COS', csstCos, csoPublicSymbol)));
        Insert( New( pSystemSymbol, Init( 'TAN', csstTAN, csoPublicSymbol)));
        Insert( New( pSystemSymbol, Init( 'COTAN', csstCOTAN, csoPublicSymbol)));
        Insert( New( pSystemSymbol, Init( 'ARCTAN', csstArcTan, csoPublicSymbol)));
        Insert( New( pSystemSymbol, Init( 'SQR', csstSQR, csoPublicSymbol)));
        Insert( New( pSystemSymbol, Init( 'SQRT', csstSQRT, csoPublicSymbol)));
        Insert( New( pSystemSymbol, Init( 'PI', csstPI, csoPublicSymbol)));

        Insert( New( pSystemSymbol, Init( 'ADDR', csstADDR, csoPublicSymbol)));
        Insert( New( pSystemSymbol, Init( 'OFS', csstOFS, csoPublicSymbol)));

        Insert( New( pSystemSymbol, Init( 'ASSIGNED', csstASSIGNED, csoPublicSymbol)));

        Insert( New( pSystemSymbol, Init( 'LOW', csstLOW, csoPublicSymbol)));
        Insert( New( pSystemSymbol, Init( 'HIGH', csstHIGH, csoPublicSymbol)));

        Insert( New( pSystemSymbol, Init( 'CONCAT', csstCONCAT, csoPublicSymbol)));

        Insert( New( pSystemSymbol, Init( 'INCLUDE', csstINCLUDE, csoPublicSymbol)));
        Insert( New( pSystemSymbol, Init( 'EXCLUDE', csstEXCLUDE, csoPublicSymbol)));

        Insert( New( pSystemSymbol, Init( 'MEM', csstMem, csoPublicSymbol)));
        Insert( New( pSystemSymbol, Init( 'MEMW', csstMemW, csoPublicSymbol)));
        Insert( New( pSystemSymbol, Init( 'MEML', csstMemL, csoPublicSymbol)));

        Insert( New( pSystemSymbol, Init( 'PORT', csstPort, csoPublicSymbol)));
        Insert( New( pSystemSymbol, Init( 'PORTW', csstPortW, csoPublicSymbol)));
        Insert( New( pSystemSymbol, Init( 'PORTL', csstPortL, csoPublicSymbol)));
        Insert( New( pSystemSymbol, Init( 'TYPEOF', csstTypeOf, csoPublicSymbol)));
      end;
  end;


function tCompiler.MakeFunctionCall( CodeTree: pCodeTree): pCodeTree;
    var
      CTree, Expr: pCodeTree;
      Line, Col: LongInt;
      ParamColl, P: pDefCollection;
      ParamOK: Boolean;
    begin
      Line := Files^.PrevLine;
      Col := Files^.PrevCol;
      Consume( ctLParen);
      ParamColl := ReverseDefColl(
        pFunctionTypeDefinition( CodeTree^.ResType)^.ParamColl);
      P := ParamColl;
      CTree := nil;
      Expr := nil;

      if Assigned( ParamColl) then
        while True do
          begin
            Expr := ReadExpression( nil);
            case ParamColl^.ParamType of
              cvtVarParam:
                ParamOK := ( GetParamType( Expr) = cvtVarParam) and
                  SameTypes( ParamColl^.Definition, Expr^.ResType);
              cvtParam,
              cvtConstParam,
              cvtStringParam:
                ParamOK :=
                  CompatibleTypes( ParamColl^.Definition, Expr^.ResType);
            end;
            if not ParamOK then
              Error( erInvalidFunctionParameters, Line, Col, '');

            if ParamColl^.ParamType <> cvtParam then
              Expr := New( pCodeTree, CreateLoadAddress( Expr, PointerDef));

            CTree := New( pCodeTree, CreateFuncParam( CTree, Expr));
            ParamColl := ParamColl^.Next;
            if Assigned( ParamColl) then
              Consume( ctComma)
            else
              break;
          end;
      DisposeDefCollection( P);

      MakeFunctionCall := New( pCodeTree, CreateFunctionCall( CodeTree, CTree,
        nil, Line, Col));

      Consume( ctRParen);
    end;

function tCompiler.GetSymbolNode( Symbol: pSymbol; Level: LongInt;
    ResultType: pDefinition; SymbolTable: pSymbolTable): pCodeTree;
  var
    CurCode: pCodeTree;
    FuncName: tNameString;
    Sym: pSymbol;
    L, C: LongInt;
  begin
    case Symbol^._Type of
      cConstSymbol:
        begin
          if not Assigned( pConstSymbol( Symbol)^.ConstType) then
            Error( erInternalError, Files^.PrevLine, Files^.PrevCol, '');
          CurCode := CreateConstCode( pConstSymbol( Symbol));
          NextToken;
        end;
      cUserOrdSymbol:
        begin
          CurCode := New( pCodeTree,
            CreateOrdConst( pUserOrdSymbol( Symbol)^.Value, pUserOrdSymbol( Symbol)^.Definition,
              Files^.PrevLine, Files^.PrevCol));
          NextToken;
        end;
      cAbsoluteSymbol:
        begin
          case pAbsoluteSymbol( Symbol)^.AbsoluteType of
            catAddress:
              begin
                NextToken;
                CurCode := New( pCodeTree, CreateMemPort( cctMem,
                  New( pCodeTree, CreateIntConst(
                    LongInt( pAbsoluteSymbol( Symbol)^.Reference),
                    LongDef, 0, 0 )),
                  pAbsoluteSymbol( Symbol)^.Definition));
              end;
            catVariable:
              begin
                CurCode := GetSymbolNode( pAbsoluteSymbol( Symbol)^.Reference, 
                  0, pAbsoluteSymbol( Symbol)^.Definition, SymbolTable);
                if CurCode^.ResType <> pAbsoluteSymbol( Symbol)^.Definition then
                  MakeTypeConversion( CurCode, pAbsoluteSymbol( Symbol)^.Definition);
              end;
          end;
        end;
      cVariableSymbol,
      cTypedConstSymbol:
        begin
          if Level = 0 then
            CurCode := New( pCodeTree,
              CreateVariable( pVariableSymbol( Symbol), Files^.PrevLine, Files^.PrevCol))
          else if Level = -1 then
            CurCode := New( pCodeTree, CreateLoadValue(
              New( pCodeTree, CreateVariable( SelfSymbol,
                Files^.PrevLine, Files^.PrevCol)),
                New( pCodeTree, CreateIntConst(
                  pVariableSymbol( Symbol)^.Offset, LongDef, 0, 0)),
                  pVariableSymbol( Symbol)^.Definition ))
          else
            CurCode := New( pCodeTree, CreateWithSymbol( Level,
              New( pCodeTree, CreateIntConst(
                pVariableSymbol( Symbol)^.Offset, LongDef, 0, 0)),
                pVariableSymbol( Symbol)^.Definition ));
          NextToken;
        end;
      cFunctionSymbol:
        begin
          FuncName := LastLine;
          Consume( ctIdentifier);
          CurCode := nil;
          if LastToken <> ctLParen then
            if Assigned( CurrentFunction) and
              Assigned( CurrentFunction^.Func) and
              (FuncName = CurrentFunction^.Func^.Name) then
              begin
                if Assigned( CurrentFunction^.Func^.Definition) and
                  Assigned( CurrentFunction^.Func^.Definition^.ResType) and
                  (CurrentFunction^.Func^.Definition^.ResType <> VoidDef) then
                  begin
                    CurCode := New( pCodeTree, CreateVariable(
                      pVariableSymbol(FindLocalSymbol( FuncResultName)), Files^.PrevLine, Files^.PrevCol))
                  end
                else
                  Error( erErrorInExpression, Files^.PrevLine, Files^.PrevCol, '');
              end
            else if Assigned( ResultType) and
              (ResultType^.DefType in [ cFunctionTypeDefinition, cAbstractDefinition]) then
              begin
                case ResultType^.DefType of
                  cFunctionTypeDefinition:
                    begin
                      Symbol := FindFunction( FuncName,
                        pFunctionTypeDefinition( ResultType)^.ParamColl, nil, Level, SymbolTable);
                      if pFunctionSymbol( Symbol)^.Definition^.CallType <>
                        pFunctionTypeDefinition( ResultType)^.CallType then
                        Symbol := nil;
                    end;
                  cAbstractDefinition:
                    if Assigned( pFunctionSymbol( Symbol)^.NextOverloaded) then
                      Symbol := nil;
                end;
                if not Assigned( Symbol) then
                  Error( erUnknownIdentifier, Files^.PrevLine, Files^.PrevCol, FuncName);
                CurCode := New( pCodeTree, CreateFunction(
                  pFunctionSymbol( Symbol), pFunctionSymbol( Symbol)^.Definition));
              end;
          if not Assigned( CurCode) then
            CurCode := ReadFunctionCall( FuncName, nil, SymbolTable)
        end;
      cTypeSymbol:
        begin
          if (NextToken <> ctPoint) or
            (pTypeSymbol( Symbol)^.Definition^.DefType <> cObjectDefinition) then
            begin
              Consume( ctLParen);
              CurCode := ReadExpression( nil);
              MakeTypeConversion( CurCode,
                pTypeSymbol(Symbol)^.Definition);
              Consume( ctRParen);
            end
          else
            begin
              Consume( ctPoint);
              if LastToken <> ctIdentifier then
                Error( erMethodIdentifierExpected,
                  Files^.PrevLine, Files^.PrevCol, '');
              Sym := pObjectDefinition( pTypeSymbol( Symbol)^.Definition)^.
                PublicSymbols^.FindSymbol( LastLine);
              if not Assigned( Sym) or (Sym^._Type <> cFunctionSymbol) or
                Assigned( pFunctionSymbol( Sym)^.NextOverloaded) then
                  Error( erMethodIdentifierExpected,
                    Files^.PrevLine, Files^.PrevCol, '');
              FuncName := LastLine;
              CurCode := nil;
              Consume( ctIdentifier);
              if {(NextToken <> ctLParen) or}
                not Assigned( CurrentObject) then
                  CurCode := New( pCodeTree, CreateFunction(
                    pFunctionSymbol( Sym),
                    pFunctionSymbol( Sym)^.Definition));
              if not Assigned( CurCode) then
                begin
                  if not IsAncestor(
                    pObjectDefinition( pTypeSymbol( Symbol)^.Definition),
                      CurrentObject) then
                        Error( erInvalidProcedureOrFunctionReference,
                          Files^.PrevLine, Files^.PrevCol, '');
                  CurCode := New( pCodeTree, CreateVariable( SelfSymbol, 0, 0));
                  CurCode^.ResType := pTypeSymbol( Symbol)^.Definition;
                  CurCode := ReadFunctionCall( FuncName, CurCode, SymbolTable);
                  CurCode^.Node.InheritedCall := True;
                end;
            end;
        end;
      cSystemSymbol:
        begin
          L := Files^.PrevLine;
          C := Files^.PrevCol;
          Consume( ctIdentifier);
          CurCode := TranslateSystemSymbol( pSystemSymbol(Symbol));
          CurCode^.Line := L;
          CurCode^.Col := C;
        end;
      cUnitSymbol:
        if not Assigned( SymbolTable) then
          begin
            NextToken;
            Consume( ctPoint);
            if LastToken <> ctIdentifier then
              Error( erIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
            Sym := pUnitSymbol( Symbol)^.UnitSymbols^.FindSymbol( LastLine);
            if not Assigned( Sym) then
              Error( erUnknownIdentifier, Files^.PrevLine, Files^.PrevCol,
                LastLine);
            CurCode := GetSymbolNode( Sym, 0, ResultType,
              pUnitSymbol( Symbol)^.UnitSymbols);
          end
        else
          Error( erErrorInStatement, Files^.PrevLine, Files^.PrevCol, '');
      else
        Error( erErrorInStatement, Files^.PrevLine, Files^.PrevCol, '');
    end;
    GetSymbolNode := CurCode;
  end;


function tCompiler.GetCodeNode( ResultType: pDefinition): pCodeTree;
  var
    L, Level: LongInt;
    R: Extended;
    I: Integer;
    FuncName: tNameString;
    CodeTree, CurCode, Tree: pCodeTree;
    Ch: Char;
    ResType: pDefinition;
    Symbol: pSymbol;
    {ConstSymbol: pConstSymbol absolute Symbol;}
    SymbolTable: pSymbolTable;
    Line, Col: LongInt;
  begin
    CurCode := nil;
    case LastToken of
      ctPlus:
        begin
          NextToken;
          CurCode := GetCodeNode( ResultType);
        end;
      ctMinus:
        begin
          NextToken;
          CurCode := New( pCodeTree, CreateNeg( nil, Files^.PrevLine, Files^.PrevCol));
          CurCode^.Left := GetCodeNode( ResultType);
        end;
      ctNot:
        begin
          Consume( ctNot);
          CurCode := New( pCodeTree, CreateNot( nil, Files^.PrevLine, Files^.PrevCol));
          CurCode^.Left := GetCodeNode( nil);
        end;

      ctNIL:
        begin
          Consume( ctNIL);
          CurCode := New( pCodeTree, CreatePointerConst( 0, nil, nil, PointerDef,
            Files^.PrevLine, Files^.PrevCol));
          if Assigned( ResultType) and
            (ResultType^.DefType = cFunctionTypeDefinition) then
            CurCode^.ResType := ResultType;
        end;

      ctAt:
        begin
          Consume( ctAt);
          {if LastToken <> ctIdentifier then
            Error( erIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');}
          {Symbol := FindSymbol( LastLine, Level);
          if not Assigned( Symbol) then
            Error( erUnknownIdentifier, Files^.PrevLine, Files^.PrevCol, '');
          case Symbol^._Type of
            cFunctionSymbol:
              if Assigned( pFunctionSymbol( Symbol)^.NextOverloaded) then
                Error( erUnknownIdentifier, Files^.PrevLine, Files^.PrevCol, '')
              else
                begin
                  CurCode := New( pCodeTree, CreateFunction(
                    pFunctionSymbol( Symbol), PointerDef));
                  Consume( ctIdentifier);
                end;
            else
              begin
                CurCode := ReadExpression( nil);
                if not (CurCode^.ResType^.DefType
                  in [ cFunctionDefinition, cFunctionTypeDefinition]) and
                  (GetParamType( CurCode) = cvtParam) then
                  Error( erVariableIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
              end;
          end;}
          CurCode := ReadExpression( VoidDef);
            if not (CurCode^.ResType^.DefType
              in [ cFunctionDefinition, cFunctionTypeDefinition]) and
              (GetParamType( CurCode) = cvtParam) then
              Error( erVariableIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
          CurCode := New( pCodeTree, CreateLoadAddress( CurCode,
            PointerDef));
        end;
      ctIntConst:
        begin
          Val( LastLine, L, I);
          CurCode := New( pCodeTree, CreateIntConst( L, LongDef, Files^.PrevLine, Files^.PrevCol));
          NextToken;
        end;
      ctRealConst:
        begin
          Val( LastLine, R, I);
          CurCode := New( pCodeTree, CreateRealConst( R, ExtendedDef, Files^.PrevLine, Files^.PrevCol));
          NextToken;
        end;
      ctCharConst:
        begin
          if LastLine[1] = '''' then
            Ch := LastLine[2]
          else if LastLine[1] = '#' then
            begin
              Val( Copy(LastLine, 2, 255), L, I);
              Ch := Char( L);
            end;
          CurCode := New( pCodeTree, CreateCharConst( Ch, CharDef, Files^.PrevLine, Files^.PrevCol));
          NextToken;
        end;
      ctStringConst:
        begin
          CurCode := New( pCodeTree, CreateStringConst( Copy(LastLine, 2,
            Length(LastLine) - 2), StringDef,Files^.PrevLine, Files^.PrevCol));
          NextToken;
        end;
      ctTrue, ctFalse:
        begin
          CurCode := New( pCodeTree, CreateBoolConst( LastToken = ctTrue, BoolDef, Files^.PrevLine, Files^.PrevCol));
          NextToken;
        end;
      ctLBracket:
        begin
          Consume( ctLBracket);
          ResType := nil;
          CurCode := nil;
          if LastToken <> ctRBracket then
            repeat
              CodeTree := ReadExpression( ResType);
              if not Assigned( ResType) then
                begin
                  if not Assigned( CodeTree^.ResType) or
                    not ( CodeTree^.ResType^.DefType in
                      [cOrdDefinition, cUserOrdDefinition]) then
                    Error( erOrdinalExpressionExpected, Files^.PrevLine, Files^.PrevCol, '')
                  else
                    ResType := CodeTree^.ResType;
                  if ResType^.DefType = cOrdDefinition then
                    if not (pOrdDefinition( ResType)^.BaseType in
                      [cbtByte, cbtChar]) then
                      ResType := ByteDef;
                end;
              if LastToken = ctPointPoint then
                begin
                  Consume( ctPointPoint);
                  Tree := ReadExpression( ResType);
                  CodeTree := New( pCodeTree, CreateSetRange( CodeTree, Tree,
                    New( pSetDefinition, Init( ResType)) ));
                end
              else
                CodeTree := New( pCodeTree, CreateSetItem( CodeTree,
                    New( pSetDefinition, Init( ResType)) ));
              CodeTree^.DisposeType := CodeTree^.DisposeType or cdtDisposeResult;
              if Assigned( CurCode) then
                begin
                  CurCode := New( pCodeTree, CreateAddition( CurCode, CodeTree,
                    New( pSetDefinition, Init( ResType)), Files^.PrevLine, Files^.PrevCol));
                  CurCode^.DisposeType := CurCode^.DisposeType or cdtDisposeResult;
                end
              else
                CurCode := CodeTree;
              case LastToken of
                ctRBracket:
                  break;
                ctComma:
                  Consume( ctComma);
                else
                  Error( erRightBracketExpected,
                    Files^.PrevLine, Files^.PrevCol, '');
              end;
            until False
          else
            begin
              ResType := New( pSetDefinition, Init( VoidDef));
              CurCode := New( pCodeTree, CreateSetConst( [], ResType,
                Files^.PrevLine, Files^.PrevCol));
              CurCode^.DisposeType := CurCode^.DisposeType or cdtDisposeResult;
            end;
          Consume( ctRBracket);
        end;

      ctNew:
        begin
          Line := Files^.PrevLine;
          Col := Files^.PrevCol;
          Consume( ctNEW);
          CurCode := ReadNew;
          CurCode^.Line := Line;
          CurCode^.Col := Col;
        end;

      ctDispose:
        begin
          Line := Files^.PrevLine;
          Col := Files^.PrevCol;
          Consume( ctDISPOSE);
          CurCode := ReadDispose;
          CurCode^.Line := Line;
          CurCode^.Col := Col;
        end;

      ctIdentifier:
        begin
          Level := 0;
          Symbol := FindSymbol( LastLine, Level);
          if Assigned( Symbol) then
            begin
              CurCode := GetSymbolNode( Symbol, Level, ResultType, nil);
            end
          else
            Error( erUnknownIdentifier, Files^.PrevLine, Files^.PrevCol, LastLine);
        end;

      ctInherited:
        begin
          if not Assigned( CurrentObject) or
          not Assigned( CurrentObject^.Ancestor) then
            Error( erNoInheritedMethodsAreAccessibleHere,
              Files^.PrevLine, Files^.PrevCol, '');
          Consume( ctInherited);
          if LastToken <> ctIdentifier then
            Error( erMethodIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
          FuncName := LastLine;
          NextToken;
          CurCode := New( pCodeTree, CreateVariable( SelfSymbol, 0, 0));
          CurCode^.ResType := CurrentObject^.Ancestor;
          CurCode := ReadFunctionCall( FuncName, CurCode, nil);
          CurCode^.Node.InheritedCall := True;
        end;

      ctLParen:
        begin
          Consume( ctLParen);
          CurCode := ReadExpression( nil);
          Consume( ctRParen);
        end;

      ctIF:
        CurCode := ReadIfExpression( ResultType);

      else
        Error( erErrorInExpression, Files^.PrevLine, Files^.PrevCol, '');
    end;

    while True do
      begin
        case LastToken of
          ctPoint:
              begin
                case CurCode^.ResType^.DefType of
                  cRecordDefinition:
                    SymbolTable := pRecordDefinition( CurCode^.ResType)^.Fields;
                  cObjectDefinition:
                    SymbolTable := pObjectDefinition( CurCode^.ResType)^.PublicSymbols;
                  else
                    Error( erInvalidQualifier, Files^.PrevLine, Files^.PrevCol, '');
                end;
                if (NextToken <> ctIdentifier) {or
                  not SymbolTable^.Search( @LastLine, I)} then
                  Error( erFieldIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '')
                else
                  begin
                    Symbol := SymbolTable^.FindSymbol( LastLine);
                    if not VisibleSymbol( Symbol) then
                      Error( erFieldIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
                    if Symbol^._Type = cVariableSymbol then
                      begin
                        CodeTree := New( pCodeTree, CreateIntConst( pVariableSymbol(Symbol)^.Offset,
                          LongDef, Files^.PrevLine, Files^.PrevCol));
                        ResType := pVariableSymbol(Symbol)^.Definition;
                        if CurCode^.Node.CodeType = cctLoadValue then
                          begin
                            Tree := New( pCodeTree, CreateAddition( nil, nil, LongDef,
                              Files^.PrevLine, Files^.PrevCol));
                            Tree^.Left := CurCode^.Right;
                            Tree^.Right := CodeTree;
                            CurCode^.Right := Tree;
                            CurCode^.ResType := ResType;
                          end
                        else
                          begin
                            Tree := New( pCodeTree, CreateLoadValue( CurCode, CodeTree, ResType));
                            CurCode := Tree;
                          end;
                        NextToken;
                      end
                    else
                      begin
                        FuncName := LastLine;
                        Consume( ctIdentifier);
                        if Assigned( ResultType) and
                          (ResultType^.DefType = cAbstractDefinition) then
                          begin
                            Dispose( CurCode, Done{$IFDEF PPRO}(){$ENDIF} );
                            CurCode := New( pCodeTree, CreateFunction(
                              pFunctionSymbol( Symbol),
                              pFunctionSymbol( Symbol)^.Definition));
                          end
                        else
                        {if NextToken = ctLParen then}
                          CurCode := ReadFunctionCall( FuncName, CurCode, nil)
                        {else if Assigned( pFunctionSymbol( Symbol)^.NextOverloaded) then
                          Error( erFieldIdentifierExpected, Files^.PrevLine, Files^.PrevCol, FuncName)}
                      end;
                  end;
              end;
          ctLBracket:
            begin
              if (CurCode^.Node.CodeType in [cctIntConst, cctOrdConst,
                cctStringConst, cctBoolConst, cctCharConst]) then
                Error( erVariableIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
              repeat
                case CurCode^.ResType^.DefType of
                  cArrayDefinition:
                    begin
                      NextToken{$IFDEF PPRO}(){$ENDIF};
                      CodeTree := New( pCodeTree, CreateMultiplication(
                        nil, nil, LongDef, Files^.PrevLine, Files^.PrevCol));
                      CodeTree^.Left := ReadExpression( pArrayDefinition( CurCode^.ResType)^.IndexDef);
                      if not CompatibleTypes( CodeTree^.Left^.ResType,
                        pArrayDefinition( CurCode^.ResType)^.IndexDef) then
                          Error( erTypeMismatch, Files^.PrevLine, Files^.PrevCol, '');
                      if IsConst( CodeTree^.Left) then
                        begin
                        case pArrayDefinition( CurCode^.ResType)^.IndexDef^.DefType of
                          cOrdDefinition:
                            if ( CodeTree^.Left^.Node.IntValue <
                              pOrdDefinition(pArrayDefinition( CurCode^.ResType)^.IndexDef)^.Min) or
                              ( CodeTree^.Left^.Node.IntValue >
                              pOrdDefinition(pArrayDefinition( CurCode^.ResType)^.IndexDef)^.Max) then
                              Error( erConstantOutOfRange, CodeTree^.Left^.Line, CodeTree^.Left^.Col, '');
                          cUserOrdDefinition:
                            if ( CodeTree^.Left^.Node.IntValue >
                              pUserOrdDefinition(pArrayDefinition( CurCode^.ResType)^.IndexDef)^.Max) then
                              Error( erConstantOutOfRange, CodeTree^.Left^.Line, CodeTree^.Left^.Col, '');
                          else
                            Error( erTypeMismatch, CodeTree^.Left^.Line, CodeTree^.Left^.Col, '');
                        end;
                          CodeTree^.Left^.Node.CodeType := cctIntConst;
                          CodeTree^.Left^.ResType := LongDef;
                        end
                      else
                        MakeTypeConversion( CodeTree^.Left, LongDef);
                      if (pArrayDefinition( CurCode^.ResType)^.IndexDef^.DefType = cOrdDefinition) and
                        (pOrdDefinition(pArrayDefinition( CurCode^.ResType)^.IndexDef)^.Min <> 0) then
                        begin
                          Tree := New( pCodeTree, CreateSubtraction(
                            nil, nil, LongDef, Files^.PrevLine, Files^.PrevCol));
                          Tree^.Left := CodeTree^.Left;
                          Tree^.Right := New( pCodeTree, CreateIntConst(
                            pOrdDefinition(pArrayDefinition( CurCode^.ResType)^.IndexDef)^.Min,
                            LongDef, Files^.PrevLine, Files^.PrevCol));
                          CodeTree^.Left := Tree;
                        end;
                      ResType := pArrayDefinition(CurCode^.ResType)^.ComponentDef;
                      CodeTree^.Right := New( pCodeTree, CreateIntConst(
                        ResType^.GetSize,
                        LongDef, Files^.PrevLine, Files^.PrevCol));
                    end;
                  cStringDefinition:
                    begin
                      NextToken;
                      CodeTree := ReadExpression( LongDef);
                      if (CodeTree^.ResType^.DefType <> cOrdDefinition) or
                        ( pOrdDefinition(CodeTree^.ResType)^.BaseType = cbtChar) then
                        Error( erIntegerExpressionExpected, CodeTree^.Line, CodeTree^.Col, '')
                      else if (CodeTree^.Node.CodeType = cctIntConst) and
                        (CodeTree^.Node.IntValue > pStringDefinition(CurCode^.ResType)^.Length) then
                        Error( erConstantOutOfRange, CodeTree^.Line, CodeTree^.Col, '');
                      ResType := CharDef;
                    end;
                  cPointerDefinition:
                    if pPointerDefinition( CurCode^.ResType)^.DefinitionType^.DefType <>
                      cObjectDefinition then
                      begin
                        NextToken;
                        CodeTree := ReadExpression( LongDef);
                        if (CodeTree^.ResType^.DefType <> cOrdDefinition) or
                          ( pOrdDefinition(CodeTree^.ResType)^.BaseType = cbtChar) then
                          Error( erIntegerExpressionExpected, CodeTree^.Line, CodeTree^.Col, '')
                        else if (CodeTree^.Node.CodeType = cctIntConst) and
                          (CodeTree^.Node.IntValue > pStringDefinition(CurCode^.ResType)^.Length) then
                          Error( erConstantOutOfRange, CodeTree^.Line, CodeTree^.Col, '');
                        ResType := pPointerDefinition( CurCode^.ResType)^.DefinitionType;
                        CurCode := New( pCodeTree, CreateDeref(
                          CurCode, ResType,
                          Files^.PrevLine, Files^.PrevCol));
                        if ResType^.GetSize <> 1 then
                          CodeTree := New( pCodeTree, CreateMultiplication(
                            CodeTree, New( pCodeTree, CreateIntConst(
                              ResType^.GetSize, LongDef,
                              Files^.PrevLine, Files^.PrevCol)),
                            LongDef,
                            Files^.PrevLine, Files^.PrevCol));
                      end
                    else
                      Error( erInvalidQualifier, Files^.PrevLine, Files^.PrevCol, '');
                  else
                    Error( erInvalidQualifier, Files^.PrevLine, Files^.PrevCol, '');
                end;
                if CurCode^.Node.CodeType = cctLoadValue then
                  begin
                    Tree := New( pCodeTree, CreateAddition( nil, nil, LongDef,
                      Files^.PrevLine, Files^.PrevCol));
                    Tree^.Left := CurCode^.Right;
                    Tree^.Right := CodeTree;
                    CurCode^.Right := Tree;
                    CurCode^.ResType := ResType;
                  end
                else
                  begin
                    Tree := New( pCodeTree, CreateLoadValue( CurCode, CodeTree, ResType));
                    CurCode := Tree;
                  end;
                if not ( LastToken in [ctRBracket, ctComma]) then
                  Error( erRightBracketExpected, Files^.PrevLine, Files^.PrevCol, '')
              until LastToken = ctRBracket;
              Consume( ctRBracket);
            end;
          ctCarret:
            begin
              OptomizeExpression( CurCode);
              ResType := CurCode^.ResType;
              if ResType^.DefType = cPointerDefinition then
                CurCode := New( pCodeTree, CreateDeref( CurCode,
                  pPointerDefinition( ResType)^.DefinitionType, Files^.PrevLine, Files^.PrevCol))
              else
                Error( erInvalidQualifier, Files^.PrevLine, Files^.PrevCol, '');
              Consume( ctCarret);
            end;
          ctLParen:
            if Assigned( CurCode^.ResType) and
              ( CurCode^.ResType^.DefType = cFunctionTypeDefinition ) and
              (LastToken = ctLParen) then
              CurCode := MakeFunctionCall( CurCode)
            else
              break;
          else
            break;
        end;
      end;
    if Assigned( ResultType) then
      case ResultType^.DefType of
        cStringDefinition:
          if (CurCode^.Node.CodeType = cctCharConst) then
            MakeTypeConversion( CurCode, ResultType);
        cPointerDefinition:
          if (pPointerDefinition( ResultType)^.DefinitionType^.DefType = cOrdDefinition) and
            (pOrdDefinition( pPointerDefinition( ResultType)^.DefinitionType)^.BaseType = cbtChar) then
            case CurCode^.Node.CodeType of
              cctCharConst:
                begin
                  CurCode^.Node.CodeType := cctPCharConst;
                  CurCode^.ResType := ResultType;
                  CurCode^.Node.StringValue := NewStr( CurCode^.Node.CharValue);
                end;
              cctStringConst:
                begin
                  CurCode^.Node.CodeType := cctPCharConst;
                  CurCode^.ResType := ResultType;
                end;
            end;
      end;
    GetCodeNode := CurCode;
  end;

function tCompiler.ReadCaseRecord( SymbolTable: pSymbolTable): LongInt;
  var
    L, Size, Max, Line, Col: LongInt;
    Pos: tIndex;
    Sym: pVariableSymbol;
    Name: String;
    CaseDef: pDefinition;
    CodeTree: pCodeTree;
    SymTable: pSymbolTable;
  begin
    Consume( ctCase);
    Size := 0;
    Max := 0;
    Name := LastLine;
    Line := Files^.PrevLine;
    Col := Files^.PrevCol;
    Consume( ctIdentifier);
    if LastToken = ctColon then
      begin
        Consume( ctColon);
        if Assigned( CurrentFunction) then
          SymTable := CurrentFunction^.Func^.Definition^.LocalSymbols
        else
          SymTable := GlobalSymbols;
        CaseDef := ReadTypeDefinition( nil, SymTable);
        if SymbolTable^.Search( Name) <> nil then
          Error( erDuplicateIdentifier, Line, Col, Name)
        else
          begin
            Sym := New( pVariableSymbol, Init( Name, CaseDef, cvtField, csoPublicSymbol));
            Sym^.Offset := SymbolTable^.DataSize;
            Size := CaseDef^.GetSize{$IFDEF PPRO}(){$ENDIF};
            SymbolTable^.Insert( Sym);
          end;
      end
    else
      begin
        Sym := pVariableSymbol(FindSymbol( Name, L));
        if not Assigned( Sym) then
          Error( erUnknownIdentifier, Line, Col, Name)
        else if Sym^._Type <> cTypeSymbol then
          Error( erTypeIdentifierExpected, Line, Col, '')
        else
          CaseDef := pTypeSymbol( Sym)^.Definition;
      end;
    Consume( ctOF);
    repeat
      Line := Files^.PrevLine;
      Col := Files^.PrevCol;
      repeat
        CodeTree := ReadExpression( CaseDef);
        if not IsConst( CodeTree) then
          Error( erCannotEvaluateThisExpression, Line, Col, '');
        Dispose( CodeTree, Done{$IFDEF PPRO}(){$ENDIF});
        if LastToken <> ctComma then
          break;
        Consume( ctComma);
      until False;
      Consume( ctColon);
      Consume( ctLParen);
      if LastToken <> ctRParen then
        Col := ReadVariables( SymbolTable, cvtField, SymbolTable^.DataSize + Size)
      else
        Col := 0;
      if Col > Max then Max := Col;
      Consume( ctRParen);
      if LastToken <> ctEND then
        Consume( ctSemicolon);
    until LastToken = ctEnd;
    ReadCaseRecord := Max + Size;
  end;

function tCompiler.ReadFunctionCall( FuncName: tNameString; ObjectCode: pCodeTree;
    SymbolTable: pSymbolTable): pCodeTree;
  var
    {FuncName: tNameString;}
    Line, Col, Lev: LongInt;
    Expr, CodeTree: pCodeTree;
    ParamColl, P: pDefCollection;
    FuncSym: pFunctionSymbol;
  begin
    {FuncName := LastLine;}
    Line := Files^.PrevLine;
    Col := Files^.PrevCol;
    CodeTree := nil;
    ParamColl := nil;
    if LastToken = ctLParen then
      begin
        Consume( ctLParen);
      while LastToken <> ctRParen do
        begin
          Expr := ReadExpression( nil);
          OptomizeExpression( Expr);
          CodeTree := New( pCodeTree, CreateFuncParam( CodeTree, Expr));
          New( P);
          P^.Definition := Expr^.ResType;
          P^.ParamType := GetParamType( Expr);
          P^.Next := ParamColl;
          ParamColl := P;
          if LastToken <> ctRParen then
            Consume( ctComma)
          else
            break;
        end;
        Consume( ctRParen);
      end;
    FuncSym := FindFunction( FuncName, ParamColl, ObjectCode, Lev, SymbolTable);
    DisposeDefCollection( ParamColl);
    if Assigned( FuncSym) then
      begin
        ParamColl := FuncSym^.Definition^.ParamColl;
        Expr := CodeTree;
        while Assigned( ParamColl) and Assigned( Expr) do
          begin
            Expr^.ResType := ParamColl^.Definition;
            MakeTypeConversion( Expr^.Right, ParamColl^.Definition);
            if ParamColl^.ParamType in [cvtVarParam, cvtConstParam] then
              begin
                Expr^.Right := New( pCodeTree, CreateLoadAddress( Expr^.Right, PointerDef));
                Expr^.ResType := PointerDef;
              end;
            ParamColl := ParamColl^.Next;
            Expr := Expr^.Left;
          end;
        if Lev = 0 then
          ObjectCode := nil
        else if Lev = -1 then
          ObjectCode := New( pCodeTree, CreateVariable( SelfSymbol, 0, 0))
        else if Lev > 0 then
          begin
            ObjectCode := New( pCodeTree, CreateWithSymbol( Lev,
              New( pCodeTree, CreateIntConst( 0, LongDef, 0, 0)),
              GetDefinition( Lev) ));
          end;
        if Assigned( ObjectCode) then
          ObjectCode := New( pCodeTree, CreateLoadAddress( ObjectCode, PointerDef));
        CodeTree := New( pCodeTree, CreateFunctionCall(
          New( pCodeTree, CreateFunction( FuncSym, nil)),
          CodeTree, ObjectCode, Line, Col));
      end
    else
      Error( erInvalidFunctionParameters, Line, Col, FuncName);
    ReadFunctionCall := CodeTree;
  end;

function tCompiler.ReadTypedConstValue( TypeDef: pDefinition; var Value: tValue): Boolean;
  var
    Line, Col: LongInt;
    Expr: pCodeTree;
  begin
    Line := Files^.PrevLine;
    Col := Files^.PrevCol;
    case TypeDef^.DefType of
      cOrdDefinition:
        begin
          Expr := ReadExpression( TypeDef);
          if not IsConst( Expr) then
            Error( erCannotEvaluateThisExpression, Line, Col, '')
          else if Expr^.ResType^.DefType = cOrdDefinition then
            begin
              if (pOrdDefinition(TypeDef)^.BaseType = cbtChar) and
                (pOrdDefinition( Expr^.ResType)^.BaseType = cbtChar) then
                begin
                  Value.ValueType := cvOrdinalValue;
                  Value.CharValue := Expr^.Node.CharValue;
                end
              else
                if (pOrdDefinition(TypeDef)^.BaseType <> cbtChar) and
                (pOrdDefinition( Expr^.ResType)^.BaseType <> cbtChar) then
                begin
                  case Expr^.Node.CodeType of
                    cctIntConst,
                    cctOrdConst:
                      begin
                        Value.ValueType := cvOrdinalValue;
                        Value.IntValue := Expr^.Node.IntValue;
                      end;
                    cctLoadAddress:
                      begin
                        Value.ValueType := cvAddressValue;
                        Value.InfoPtr := CreatePointerValue( Expr);
                      end;
                  end;
                end
              else
                Error( erTypeMismatch, Line, Col, '');
            end
          else
            Error( erTypeMismatch, Line, Col, '');
          Dispose( Expr, Done);
        end;
      cUserOrdDefinition:
        begin
          Expr := ReadExpression( TypeDef);
          if not IsConst( Expr) then
            Error( erCannotEvaluateThisExpression, Line, Col, '')
          else if Expr^.ResType <> TypeDef then
            Error( erTypeMismatch, Line, Col, '')
          else
            begin
              Value.ValueType := cvOrdinalValue;
              Value.IntValue := Expr^.Node.OrdValue;
            end;
          Dispose( Expr, Done);
        end;
      cBooleanDefinition:
        begin
          Expr := ReadExpression( TypeDef);
          if not IsConst( Expr) then
            Error( erCannotEvaluateThisExpression, Line, Col, '')
          else if Expr^.ResType^.DefType <> cBooleanDefinition then
            Error( erTypeMismatch, Line, Col, '')
          else
            begin
              Value.ValueType := cvOrdinalValue;
              Value.BoolValue := Expr^.Node.BoolValue;
            end;
          Dispose( Expr, Done);
        end;
      cRealDefinition:
        begin
          Expr := ReadExpression( TypeDef);
          if not IsConst( Expr) then
            Error( erCannotEvaluateThisExpression, Line, Col, '')
          else if Expr^.ResType^.DefType <> cRealDefinition then
            Error( erTypeMismatch, Line, Col, '')
          else
            begin
              Value.ValueType := cvRealValue;
              Value.RealValue := Expr^.Node.RealValue;
            end;
          Dispose( Expr, Done);
        end;
      cPointerDefinition:
        begin
          Expr := ReadExpression( TypeDef);
          if not IsConst( Expr) then
            Error( erCannotEvaluateThisExpression, Line, Col, '')
          else if Expr^.ResType^.DefType <> cPointerDefinition then
            Error( erTypeMismatch, Line, Col, '')
          else if Expr^.Node.CodeType <> cctPCharConst then
            begin
              Value.ValueType := cvAddressValue;
              Value.InfoPtr := CreatePointerValue( Expr);
            end
          else
            begin
              Value.ValueType := cvASCIIZValue;
              if Assigned( Expr^.Node.StringValue) then
                Value.InfoPtr := NewStr( Expr^.Node.StringValue^)
              else
                Value.InfoPtr := nil;
            end;
          Dispose( Expr, Done);
        end;
      cStringDefinition:
        begin
          Expr := ReadExpression( TypeDef);
          if not IsConst( Expr) then
            Error( erCannotEvaluateThisExpression, Line, Col, '')
          else if Expr^.ResType^.DefType <> cStringDefinition then
            Error( erTypeMismatch, Line, Col, '')
          else
            begin
              Value.ValueType := cvStringValue;
              Value.StringValue :=
                NewStr( Copy( Expr^.Node.StringValue^, 1, pStringDefinition(TypeDef)^.Length));
            end;
          Dispose( Expr, Done);
        end;
      cRecordDefinition:
        begin
          Value.ValueType := cvRecordValue;
          Value.InfoPtr := ReadRecordConst( pRecordDefinition(TypeDef));
        end;
      cArrayDefinition:
        begin
          Value.ValueType := cvArrayValue;
          Value.InfoPtr := ReadArrayConst( pArrayDefinition(TypeDef),
            Value.ValueType);
        end;
      cSetDefinition:
        begin
          Expr := ReadExpression( TypeDef);
          if not IsConst( Expr) then
            Error( erCannotEvaluateThisExpression, Line, Col, '')
          else if Assigned( Expr) then
            begin
              Value.ValueType := cvSetValue;
              Value.InfoPtr := Expr^.Node.SetValue;
              Expr^.Node.SetValue := nil;
              Dispose( Expr, Done);
            end;
        end;
      cFunctionTypeDefinition:
        begin
          Expr := ReadExpression( TypeDef);
          if not IsConst( Expr) then
            Error( erCannotEvaluateThisExpression, Line, Col, '')
          {else if Expr^.ResType^.DefType <> cPointerDefinition then
            Error( erTypeMismatch, Line, Col, '')}
          else
            begin
              if Expr^.Node.CodeType = cctFunction then
                Expr := New( pCodeTree, CreateLoadAddress( Expr, TypeDef));
              Value.ValueType := cvProceduralValue;
              Value.InfoPtr := CreatePointerValue( Expr);
            end;
          Dispose( Expr, Done{$IFDEF PPRO}(){$ENDIF});
        end;
    end;
    ReadTypedConstValue := True;
  end;

function tCompiler.ReadArrayConst( TypeDef: pArrayDefinition; var ValType: Integer): Pointer;
  var
    Value: tValue;
    CompDef: pDefinition;
    I, Count: LongInt;
    Data: pValueArray;
    CodeTree: pCodeTree;
  begin
    CompDef := pArrayDefinition( TypeDef)^.ComponentDef;
    Count := TypeDef^.GetCount;
    if (CompDef^.DefType = cOrdDefinition) and
      (pOrdDefinition( CompDef)^.BaseType = cbtChar) and
      (LastToken <> ctLParen) then
      begin
        GetMem( Data, Count);
        FillChar( Data^, Count, 0);
        CodeTree := ReadExpression( nil);
        if (CodeTree^.ResType^.DefType <> cStringDefinition) then
          Error( erStringExpressionExpected, Files^.PrevLine, Files^.PrevCol, '');
        if CodeTree^.Node.CodeType <> cctStringConst then
          Error( erCannotEvaluateThisExpression, Files^.PrevLine, Files^.PrevCol, '');
        if Count > Length( CodeTree^.Node.StringValue^) then
          Count := Length( CodeTree^.Node.StringValue^);
        Move( CodeTree^.Node.StringValue^[ 1], Data^, Count);
        Dispose( CodeTree, Done);
        ReadArrayConst := Data;
        ValType := cvCharArrayValue;
        Exit;
      end;
    Consume( ctLParen);
    GetMem( Data, Count * SizeOf( tValue) );
    FillChar( Data^, Count * SizeOf( tValue), 0);
    for I := 0 to Count - 1 do
      begin
        if I <> 0 then
          Consume( ctComma);
        ReadTypedConstValue( CompDef, Value);
        Data^[ I] := Value;
      end;
    Consume( ctRParen);
    ReadArrayConst := Data;
  end;

function tCompiler.ReadRecordConst( TypeDef: pRecordDefinition): Pointer;
  var
    Value: tValue;
    Count: LongInt;
    I: tIndex;
    Data: pValueArray;
    StrColl: pStringCollection;
    Sym: pVariableSymbol;
  begin
    if not Consume( ctLParen) then
      begin
        ReadRecordConst := nil;
        Exit;
      end;
    GetMem( Data, TypeDef^.GetCount{$IFDEF PPRO}(){$ENDIF} * SizeOf( tValue));
    FillChar( Data^, TypeDef^.GetCount{$IFDEF PPRO}(){$ENDIF} * SizeOf( tValue), 0);
    Count := 0;
    if LastToken <> ctIdentifier then
      Error( erFieldIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '')
    else
    StrColl := New( pStringCollection, Init( 5, 5));
    repeat
      Sym := TypeDef^.Fields^.Search( LastLine);
      if Assigned( Sym) then
        begin
          if StrColl^.Search( @LastLine, I) then
            begin
              Error( erInvalidOrderingOfFields, Files^.PrevLine, Files^.PrevCol, '');
              break;
            end
          else
            begin
              StrColl^.Insert( NewStr( LastLine));
              Consume( ctIdentifier);
              Consume( ctColon);
              ReadTypedConstValue( Sym^.Definition, Value);
              Data^[ TypeDef^.Fields^.IndexOf( Sym)] := Value;
            end;
        end
      else
        break;
      if LastToken = ctSemicolon then
        Consume( ctSemicolon);
    until LastToken <> ctIdentifier;
    Consume( ctRParen);
    Dispose( StrColl, Done{$IFDEF PPRO}(){$ENDIF});
    ReadRecordConst := Data;
  end;

function tCompiler.ReadIfStatement: pCodeTree;
  var
    Condition, IfBlock, ElseBlock: pCodeTree;
  begin
    Consume( ctIF);
    Condition := ReadExpression( BoolDef);
    if Condition^.ResType^.DefType <> cBooleanDefinition then
      Error( erBooleanExpressionExpected, Files^.PrevLine, Files^.PrevCol, '');
    Consume( ctTHEN);
    IFBlock := nil;
    ELSEBlock := nil;
    ReadStatement( IFBlock);
    if LastToken = ctELSE then
      begin
        Consume( ctELSE);
        ReadStatement( ELSEBlock);
      end;
    ReadIfStatement := New( pCodeTree, CreateIFBlock( Condition, IFBlock, ELSEBlock));
  end;

function tCompiler.ReadWhileStatement: pCodeTree;
  var
    Condition, Loop: pCodeTree;
  begin
    ReadWhileStatement := nil;
    Consume( ctWHILE);
    Condition := ReadExpression( BoolDef);
    if Condition^.ResType^.DefType <> cBooleanDefinition then
      Error( erBooleanExpressionExpected, Files^.PrevLine, Files^.PrevCol, '');
    Consume( ctDO);
    Inc( LoopLevel);
    Loop := nil;
    if LastToken <> ctSemicolon then
      ReadStatement( Loop);
    Dec( LoopLevel);
    ReadWhileStatement := New( pCodeTree, CreateWhileBlock(
      Condition, Loop));
  end;

function tCompiler.ReadRepeatUntilStatement: pCodeTree;
  var
    CurCode, Condition, Loop: pCodeTree;
  begin
    ReadRepeatUntilStatement := nil;
    Consume( ctRepeat);
    Inc( LoopLevel);
    Loop := nil;
    CurCode := Loop;
    while LastToken <> ctUNTIL do
      begin
        if Assigned( Loop) then
          begin
            ReadStatement( CurCode^.Left);
            if Assigned( CurCode^.Left) then CurCode := CurCode^.Left;
          end
        else
          begin
            ReadStatement( Loop);
            CurCode := Loop;
          end;
        if LastToken <> ctUNTIL then
          Consume( ctSemicolon);
      end;
    Consume(ctUNTIL);
    Dec( LoopLevel);
    Condition := ReadExpression( BoolDef);
    if not Assigned( Condition) or
      (Condition^.ResType^.DefType <> cBooleanDefinition) then
      Error( erBooleanExpressionExpected, Files^.PrevLine, Files^.PrevCol, '');
    ReadRepeatUntilStatement := New( pCodeTree, CreateRepeatUntilBlock(
      Condition, Loop));
  end;

function tCompiler.ReadForStatement: pCodeTree;
  var
    Min, Max, Loop, Counter: pCodeTree;
    Sym: pVariableSymbol;
    IsForward: Boolean;
  begin
    Inc( TempLevel);
    ReadForStatement := nil;
    Consume( ctFOR);
    if LastToken <> ctIdentifier then
      Error( erIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
    {Sym := pVariableSymbol( FindSymbol( LastLine));}
    Counter := GetCodeNode( nil);
    if Assigned( Counter) and
      not (Counter^.ResType^.DefType in [cOrdDefinition, cUserOrdDefinition]) then
      Error( erInvalidFORControlVariable, Files^.PrevLine, Files^.PrevCol, '');
    {if not Assigned( Counter) then
      Error( erUnknownIdentifier, Files^.PrevLine, Files^.PrevCol);
    if not (Sym^._Type in [cVariableSymbol, cTypedConstSymbol]) then
      Error( erVariableIdentifierExpected, Files^.PrevLine, Files^.PrevCol);
    if not (Counter^.Definition^.DefType in [cOrdDefinition, cUserOrdDefinition]) then
      Error( erInvalidFORControlVariable, Files^.PrevLine, Files^.PrevCol);}
    {New( pCodeTree, CreateVariable( Sym, Files^.PrevLine, Files^.PrevCol));}
    {Consume( ctIdentifier);}
    Consume( ctAssignment);
    Min := ReadExpression( Counter^.ResType);
    if not CompatibleTypes( Counter^.ResType, Min^.ResType) then
      Error( erTypeMismatch, Files^.PrevLine, Files^.PrevCol, '');
    if LastToken = ctTO then
      begin
        IsForward := True;
        Consume( ctTO);
      end
    else
      begin
        IsForward := False;
        Consume( ctDownTo);
      end;
    Max := ReadExpression( Counter^.ResType);
    if not CompatibleTypes( Counter^.ResType, Max^.ResType) then
      Error( erTypeMismatch, Files^.PrevLine, Files^.PrevCol, '');
    Consume( ctDO);
    Inc( LoopLevel);
    Loop := nil;
    if LastToken <> ctSemicolon then
      ReadStatement( Loop);
    Dec( LoopLevel);
    ReadFORStatement := New( pCodeTree, CreateFORBlock( Counter, Min, Max,
      Loop, IsForward));
    Dec( TempLevel);
  end;

function tCompiler.ReadCaseStatement: pCodeTree;
  var
    Expr, ElseBlock, CaseNode, CurCode, CodeTree: pCodeTree;
    pCode: ^pCodeTree;
    L1, L2: LongInt;
  begin
    Consume( ctCASE);
    L1 := Files^.PrevLine;
    L2 := Files^.PrevCol;
    Expr := ReadExpression( nil);
    if not Assigned( Expr) or not Assigned( Expr^.ResType) then
      Error( erInternalError, Files^.PrevLine, Files^.PrevCol, '');
    if not (Expr^.ResType^.DefType in [ cOrdDefinition, cUserOrdDefinition]) then
      Error( erOrdinalExpressionExpected, Files^.PrevLine, Files^.PrevCol, '');
    Expr^.Line := L1;
    Expr^.Col := L2;
    ElseBlock := nil;
    Consume( ctOF);
    CaseNode := nil;
    pCode := @CaseNode;
    repeat
      CodeTree := nil;
      repeat
        CurCode := ReadExpression( Expr^.ResType);
        if not IsConst( CurCode) then
          Error( erCannotEvaluateThisExpression, Files^.PrevLine, Files^.PrevCol, '');
        L1 := CurCode^.Node.IntValue;
        Dispose( CurCode, Done);
        if LastToken = ctPointPoint then
          begin
            Consume( ctPointPoint);
            CurCode := ReadExpression( Expr^.ResType);
            if not IsConst( CurCode) then
              Error( erCannotEvaluateThisExpression, Files^.PrevLine, Files^.PrevCol, '');
            L2 := CurCode^.Node.IntValue;
            Dispose( CurCode, Done);
            CodeTree := New( pCodeTree, CreateCaseBetween( L1, L2, CodeTree));
          end
        else
          begin
            CodeTree := New( pCodeTree, CreateCaseEqual( L1, CodeTree));
          end;
        case LastToken of
          ctColon:
            begin
              Consume( ctColon);
              break;
            end;
          ctComma:
            begin
              Consume( ctComma);
            end;
          else
            Error( erErrorInStatement, Files^.PrevLine, Files^.PrevCol, '');
        end;
      until False;
      if LastToken <> ctSemicolon then
        ReadStatement( CurCode)
      else
        CurCode := nil;
      Consume( ctSemicolon);
      pCode^ := New( pCodeTree, CreateCaseNode( CodeTree, CurCode, nil));
      pCode := @pCode^^.Left;
    until (LastToken = ctELSE) or (LastToken = ctEND);
    ElseBlock := nil;
    if LastToken = ctELSE then
      begin
        Consume( ctELSE);
        if LastToken <> ctSemicolon then
          ReadStatement( ElseBlock);
        if LastToken = ctSemicolon then
          Consume( ctSemicolon);
      end;
    Consume( ctEND);
    ReadCaseStatement := New( pCodeTree, CreateCaseBlock( Expr, CaseNode, ElseBlock));
  end;

function tCompiler.TranslateSystemSymbol( Symbol: pSystemSymbol): pCodeTree;
  var
    ResCode: pCodeTree;
  begin
    ResCode := nil;
    case Symbol^.SystemType of
      csstWriteLn,
      csstWrite:
        begin
          ResCode := TranslateWrite( Symbol^.SystemType);
        end;

      csstReadLn,
      csstRead:
        begin
          ResCode := TranslateRead( Symbol^.SystemType);
        end;

      csstSizeOf:
        begin
          ResCode := TranslateSizeOf{$IFDEF PPRO}(){$ENDIF};
        end;

      csstChr:
        ResCode := TranslateChr{$IFDEF PPRO}(){$ENDIF};

      csstOrd:
        ResCode := TranslateOrd{$IFDEF PPRO}(){$ENDIF};

      csstPred,
      csstSucc:
        ResCode := TranslatePredSucc( Symbol^.SystemType);

      csstStr:
        ResCode := TranslateStr{$IFDEF PPRO}(){$ENDIF};

      csstInc,
      csstDec:
        ResCode := TranslateIncDec( Symbol^.SystemType);

      csstOfs:
        ResCode := TranslateOfs{$IFDEF PPRO}(){$ENDIF};

      csstLength:
        ResCode := TranslateLength{$IFDEF PPRO}(){$ENDIF};

      csstAssign:
        ResCode := TranslateAssign{$IFDEF PPRO}(){$ENDIF};

      csstABS:
        ResCode := TranslateABS{$IFDEF PPRO}(){$ENDIF};

      csstODD:
        ResCode := TranslateODD{$IFDEF PPRO}(){$ENDIF};

      csstADDR:
        ResCode := TranslateADDR{$IFDEF PPRO}(){$ENDIF};

      csstTypeOf:
        ResCode := TranslateTypeOf{$IFDEF PPRO}(){$ENDIF};

      csstAssigned:
        ResCode := TranslateAssigned{$IFDEF PPRO}(){$ENDIF};

      csstLow:
        ResCode := TranslateLow{$IFDEF PPRO}(){$ENDIF};

      csstHigh:
        ResCode := TranslateHigh{$IFDEF PPRO}(){$ENDIF};

      csstConcat:
        ResCode := TranslateConcat{$IFDEF PPRO}(){$ENDIF};

      csstInclude:
        ResCode := TranslateIncludeExclude( cctInclude);

      csstExclude:
        ResCode := TranslateIncludeExclude( cctExclude);

      csstSin,
      csstCos,
      csstTan,
      csstCotan,
      csstArcTan,
      csstSqr,
      csstSqrt:
        ResCode := TranslateFloat( Symbol^.SystemType);

      csstPI:
        ResCode := New( pCodeTree, CreateRealConst( PI, ExtendedDef, 0, 0));

      csstMem:
        ResCode := TranslateMemPort( cctMem, ByteDef);
      csstMemW:
        ResCode := TranslateMemPort( cctMem, WordDef);
      csstMemL:
        ResCode := TranslateMemPort( cctMem, DWordDef);
      csstPort:
        ResCode := TranslateMemPort( cctPort, ByteDef);
      csstPortW:
        ResCode := TranslateMemPort( cctPort, WordDef);
      csstPortL:
        ResCode := TranslateMemPort( cctPort, DWordDef);
    end;
    TranslateSystemSymbol := ResCode;
  end;

function tCompiler.TranslateWrite( Symbol: tSystemSymbolType): pCodeTree;
  var
    CurCode, FileCode, ResCode, WidthCode, DigsCode: pCodeTree;
    CodeTree: ^pCodeTree;
    Sym: pVariableSymbol;
    L: LongInt;
  begin
    ResCode := nil;
    CodeTree := @ResCode;
    Sym := nil;
    FileCode := nil;
    if (LastToken = ctLParen) or (Symbol = csstWrite) then
      begin
    Consume( ctLParen);
    repeat
            CurCode := ReadExpression( nil);
            if (CurCode^.ResType^.DefType = cFileDefinition) then
              begin
                if not Assigned( FileCode) then
                  FileCode := CurCode;
                if not Assigned( FileCode) or
                  not Assigned( FileCode^.ResType) then
                  Error( erInvalidFileType, Files^.PrevLine, Files^.PrevCol, '');
                if ( pFileDefinition( FileCode^.ResType)^.FileType = cftUntyped ) or
                  ((pFileDefinition(FileCode^.ResType)^.FileType <> cftTextFile) and
                  (Symbol = csstWriteLn)) then
                  Error( erInvalidFileType, Files^.PrevLine, Files^.PrevCol, '');
                if (Symbol = csstWriteLn) and (LastToken = ctRParen) then
                  break;
                Consume( ctComma);
                continue;
              end
            else
              begin
                if not Assigned( FileCode) then
                  begin
                    if csCompileSystem in Switches then
                      Sym := pVariableSymbol( FindSymbol( 'OUTPUT', L))
                    else
                      begin
                        Sym := pVariableSymbol( FindSymbol('SYSTEM', L));
                        if Assigned( Sym) and ( Sym^._Type = cUnitSymbol) then
                          Sym := pVariableSymbol( pUnitSymbol(
                            Sym)^.UnitSymbols^.FindSymbol('OUTPUT') );
                      end;
                    if not Assigned( Sym) or ( not Assigned( Sym^.Definition)) or
                      (Sym^.Definition^.DefType <> cFileDefinition) then
                      Error( erInternalError, Files^.PrevLine, Files^.PrevCol, '');
                    FileCode := New( pCodeTree, CreateVariable( Sym, 0, 0));
                  end;
                case pFileDefinition(FileCode^.ResType)^.FileType of
                  cftTextFile:
                    begin
                      Sym := nil;
                      case CurCode^.ResType^.DefType of
                        cOrdDefinition:;
                        cRealDefinition:
                          begin
                            MakeTypeConversion( CurCode, ExtendedDef);
                          end;
                        cBooleanDefinition:
                          begin
                            MakeTypeConversion( CurCode, BoolDef);
                          end;
                        cStringDefinition:
                          begin
                            MakeTypeConversion( CurCode, StringDef);
                            CurCode := New( pCodeTree, CreateLoadAddress(
                              CurCode, PointerDef));
                          end;
                        else
                          Error( erTypeMismatch, Files^.PrevLine, Files^.PrevCol, '');
                      end;

                      if LastToken = ctColon then
                        begin
                          Consume( ctColon);
                          WidthCode := ReadExpression( LongDef);
                          if not Assigned( WidthCode) or
                            not Assigned( WidthCode^.ResType) or
                            (WidthCode^.ResType^.DefType <> cOrdDefinition) or
                            (pOrdDefinition( WidthCode^.ResType)^.BaseType = cbtChar) then
                            Error( erIntegerExpressionExpected, Files^.PrevLine, Files^.PrevCol, '');
                        end
                      else
                        WidthCode := New( pCodeTree, CreateIntConst( 0, LongDef, Files^.PrevLine, Files^.PrevCol));

                      DigsCode := nil;
                      if CurCode^.ResType^.DefType = cRealDefinition then
                        begin
                          if LastToken = ctColon then
                            begin
                              Consume( ctColon);
                              DigsCode := ReadExpression( LongDef);
                              if not Assigned( DigsCode) or
                                not Assigned( DigsCode^.ResType) or
                                (DigsCode^.ResType^.DefType <> cOrdDefinition) or
                                (pOrdDefinition( DigsCode^.ResType)^.BaseType = cbtChar) then
                                  Error( erIntegerExpressionExpected, Files^.PrevLine, Files^.PrevCol, '');
                            end
                          else
                            DigsCode := New( pCodeTree, CreateIntConst( -18, LongDef, Files^.PrevLine, Files^.PrevCol));
                        end;
                      CodeTree^ := New( pCodeTree, CreateWriteParam(
                        CurCode, WidthCode, DigsCode));

                      CodeTree := @CodeTree^^.Left;
                    end;
                  cftUntyped:
                    begin
                    end;

                  cftTyped:
                    begin
                      if GetParamType( CurCode) <> cvtVarParam then
                        Error( erVariableIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
                      if not SameTypes(
                        pFileDefinition( FileCode^.ResType)^.FileDef,
                        CurCode^.ResType) then
                        Error( erTypeMismatch, Files^.PrevLine, Files^.PrevCol, '');
                      CodeTree^ := New( pCodeTree, CreateWriteParam(
                        New( pCodeTree, CreateLoadAddress( CurCode, PointerDef)),
                        nil, nil));
                      CodeTree := @CodeTree^^.Left;
                    end;

                end;
              end;
            if LastToken <> ctRParen then
              Consume( ctComma)
            else
              break;
    until False;
    Consume( ctRParen);
      end
    else
      begin
        Sym := nil;
        if csCompileSystem in Switches then
          Sym := pVariableSymbol( FindSymbol( 'OUTPUT', L))
        else
          begin
            Sym := pVariableSymbol( FindSymbol('SYSTEM', L));
            if Assigned( Sym) and ( Sym^._Type = cUnitSymbol) then
              Sym := pVariableSymbol( pUnitSymbol(
                Sym)^.UnitSymbols^.FindSymbol('OUTPUT') );
          end;
        if not Assigned( Sym) or ( not Assigned( Sym^.Definition)) or
          (Sym^.Definition^.DefType <> cFileDefinition) then
          Error( erInternalError, Files^.PrevLine, Files^.PrevCol, '');
        FileCode := New( pCodeTree, CreateVariable( Sym, 0, 0));
      end;
    if Symbol = csstWriteLn then
      begin
        if not Assigned( FileCode) or
          not Assigned( FileCode^.ResType) or
          (pFileDefinition(FileCode^.ResType)^.FileType <> cftTextFile) then
            Error( erInvalidFileType, Files^.PrevLine, Files^.PrevCol, '');
        ResCode := New( pCodeTree, CreateWriteLn( FileCode, ResCode));
      end
    else
      ResCode := New( pCodeTree, CreateWrite( FileCode, ResCode));
    TranslateWrite := ResCode;
  end;

function tCompiler.TranslateRead( Symbol: tSystemSymbolType): pCodeTree;
  var
    CurCode, FileCode, ResCode: pCodeTree;
    CodeTree: ^pCodeTree;
    Sym: pVariableSymbol;
    L: LongInt;
  begin
    ResCode := nil;
    CodeTree := @ResCode;
    Sym := nil;
    FileCode := nil;
    if (LastToken = ctLParen) or (Symbol = csstWrite) then
      begin
    Consume( ctLParen);
    repeat
            CurCode := ReadExpression( nil);
            if (CurCode^.ResType^.DefType = cFileDefinition) then
              begin
                if not Assigned( FileCode) then
                  FileCode := CurCode;
                if not Assigned( FileCode) or
                  not Assigned( FileCode^.ResType) then
                  Error( erInvalidFileType, Files^.PrevLine, Files^.PrevCol, '');
                if ( pFileDefinition( FileCode^.ResType)^.FileType = cftUntyped ) or
                  ((pFileDefinition(FileCode^.ResType)^.FileType <> cftTextFile) and
                  (Symbol = csstReadLn)) then
                  Error( erInvalidFileType, Files^.PrevLine, Files^.PrevCol, '');
                if (Symbol = csstReadLn) and (LastToken = ctRParen) then
                  break;
                Consume( ctComma);
                continue;
              end
            else
              begin
                if not Assigned( FileCode) then
                  begin
                    if csCompileSystem in Switches then
                      Sym := pVariableSymbol( FindSymbol( 'INPUT', L))
                    else
                      begin
                        Sym := pVariableSymbol( FindSymbol('SYSTEM', L));
                        if Assigned( Sym) and ( Sym^._Type = cUnitSymbol) then
                          Sym := pVariableSymbol( pUnitSymbol(
                            Sym)^.UnitSymbols^.FindSymbol('INPUT') );
                      end;
                    if not Assigned( Sym) or ( not Assigned( Sym^.Definition)) or
                      (Sym^.Definition^.DefType <> cFileDefinition) then
                      Error( erInternalError, Files^.PrevLine, Files^.PrevCol, '');
                    FileCode := New( pCodeTree, CreateVariable( Sym, 0, 0));
                  end;
                case pFileDefinition(FileCode^.ResType)^.FileType of
                  cftTextFile:
                    begin
                      if GetParamType( CurCode) <> cvtVarParam then
                        Error( erVariableIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');

                      case CurCode^.ResType^.DefType of
                        cOrdDefinition:;
                        cRealDefinition:;
                        cBooleanDefinition:;
                        cStringDefinition:;
                        else
                          Error( erTypeMismatch, Files^.PrevLine, Files^.PrevCol, '');
                      end;

                      {CodeTree^ := New( pCodeTree, CreateFuncParam( nil,
                        CurCode));

                      CodeTree := @CodeTree^^.Left;}
                    end;
                  cftUntyped:
                    begin
                    end;

                  cftTyped:
                    begin
                      if GetParamType( CurCode) <> cvtVarParam then
                        Error( erVariableIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
                      if not SameTypes(
                        pFileDefinition( FileCode^.ResType)^.FileDef,
                        CurCode^.ResType) then
                        Error( erTypeMismatch, Files^.PrevLine, Files^.PrevCol, '');
                    end;

                end;

                CodeTree^ := New( pCodeTree, CreateFuncParam( nil, CurCode ));
                CodeTree := @CodeTree^^.Left;
              end;
            if LastToken <> ctRParen then
              Consume( ctComma)
            else
              break;
    until False;
    Consume( ctRParen);
      end
    else
      begin
        Sym := nil;
        if csCompileSystem in Switches then
          Sym := pVariableSymbol( FindSymbol( 'INPUT', L))
        else
          begin
            Sym := pVariableSymbol( FindSymbol('SYSTEM', L));
            if Assigned( Sym) and ( Sym^._Type = cUnitSymbol) then
              Sym := pVariableSymbol( pUnitSymbol(
                Sym)^.UnitSymbols^.FindSymbol('INPUT') );
          end;
        if not Assigned( Sym) or ( not Assigned( Sym^.Definition)) or
          (Sym^.Definition^.DefType <> cFileDefinition) then
          Error( erInternalError, Files^.PrevLine, Files^.PrevCol, '');
        FileCode := New( pCodeTree, CreateVariable( Sym, 0, 0));
      end;
    if Symbol = csstReadLn then
      begin
        if not Assigned( FileCode) or
          not Assigned( FileCode^.ResType) or
          (pFileDefinition(FileCode^.ResType)^.FileType <> cftTextFile) then
            Error( erInvalidFileType, Files^.PrevLine, Files^.PrevCol, '');
        ResCode := New( pCodeTree, CreateReadLn( FileCode, ResCode));
      end
    else
      ResCode := New( pCodeTree, CreateRead( FileCode, ResCode));
    TranslateRead := ResCode;
  end;

function tCompiler.TranslateSizeOf: pCodeTree;
  var
    Sym: pSymbol;
    Def: pDefinition;
    L: LongInt;
  begin
    Consume( ctLParen);
    if LastToken <> ctIdentifier then
      Error( erVariableIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
    Sym := FindSymbol( LastLine, L);
    if not Assigned( Sym) then
      Error( erUnknownIdentifier, Files^.PrevLine, Files^.PrevCol, LastLine);
    case Sym^._Type of
      cTypeSymbol:
        Def := pTypeSymbol( Sym)^.Definition;
      cVariableSymbol,
      cTypedConstSymbol,
      cAbsoluteSymbol:
        Def := pVariableSymbol( Sym)^.Definition;
      else
        Error( erVariableIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
    end;
    Consume( ctIdentifier);
    while True do
      begin
        if not Assigned( Def) then
          Error( erInternalError, Files^.PrevLine, Files^.PrevCol, '');
        case LastToken of
          ctPoint:
            begin
              if Def^.DefType <> cRecordDefinition then
                Error( erRightParenExpected, Files^.PrevLine, Files^.PrevCol, '');
              Consume( ctPoint);
              if LastToken <> ctIdentifier then
                Error( erFieldIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
              Sym := pRecordDefinition( Def)^.Fields^.FindSymbol( LastLine);
              if not Assigned( Sym) then
                Error( erFieldIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
              if Sym^._Type <> cVariableSymbol then
                Error( erInternalError, Files^.PrevLine, Files^.PrevCol, '');
              Def := pVariableSymbol( Sym)^.Definition;
              Consume( ctIdentifier);
            end;
          ctLBracket:
            begin
              if not (Def^.DefType in [cArrayDefinition, cStringDefinition]) then
                Error( erRightParenExpected, Files^.PrevLine, Files^.PrevCol, '');
              Consume( ctLBracket);
              repeat
                case Def^.DefType of
                  cArrayDefinition:
                    Def := pArrayDefinition( Def)^.ComponentDef;
                  cStringDefinition:
                    Def := CharDef;
                  else
                    Error( erRightBracketExpected, Files^.PrevLine, Files^.PrevCol, '');
                end;
                if not Assigned( Def) then
                  Error( erInternalError, Files^.PrevLine, Files^.PrevCol, '');
                if LastToken = ctComma then
                  Consume( ctComma)
                else
                  break;
              until False;
              Consume( ctRBracket);
            end;
          ctCarret:
            begin
              if Def^.DefType <> cPointerDefinition then
                Error( erRightParenExpected, Files^.PrevLine, Files^.PrevCol, '');
              Consume( ctCarret);
              Def := pPointerDefinition( Def)^.DefinitionType;
            end;
          else
            break;
        end;
      end;
    if not Assigned( Def) then
      Error( erInternalError, Files^.PrevLine, Files^.PrevCol, '');
    Consume( ctRParen);
    TranslateSizeOf := New( pCodeTree, CreateIntConst( Def^.GetSize{$IFDEF PPRO}(){$ENDIF},
      LongDef, Files^.PrevLine, Files^.PrevCol));
  end;

function tCompiler.TranslateChr: pCodeTree;
  var
    Expr: pCodeTree;
    Line, Col: LongInt;
  begin
    Consume( ctLParen);
    Line := Files^.PrevLine;
    Col := Files^.PrevCol;
    Expr := ReadExpression( nil);
    if not Assigned( Expr) or not Assigned( Expr^.ResType) or
      (Expr^.ResType^.DefType <> cOrdDefinition) or
      (pOrdDefinition( Expr^.ResType)^.BaseType = cbtChar) then
      Error( erIntegerExpressionExpected, Line, Col, '');
    MakeTypeConversion( Expr, CharDef);
    Consume( ctRParen);
    TranslateChr := Expr;
  end;

function tCompiler.TranslateOrd: pCodeTree;
  var
    Expr: pCodeTree;
    Line, Col: LongInt;
  begin
    Consume( ctLParen);
    Line := Files^.PrevLine;
    Col := Files^.PrevCol;
    Expr := ReadExpression( nil);
    if not Assigned( Expr) or not Assigned( Expr^.ResType) or
      not (Expr^.ResType^.DefType in [cOrdDefinition, cUserOrdDefinition, cBooleanDefinition]) then
      Error( erOrdinalExpressionExpected, Line, Col, '');
    MakeTypeConversion( Expr, LongDef);
    Consume( ctRParen);
    TranslateOrd := Expr;
  end;

function tCompiler.TranslatePredSucc( Symbol: tSystemSymbolType): pCodeTree;
  var
    Expr: pCodeTree;
    Line, Col: LongInt;
  begin
    Consume( ctLParen);
    Line := Files^.PrevLine;
    Col := Files^.PrevCol;
    Expr := ReadExpression( nil);
    if not Assigned( Expr) or not Assigned( Expr^.ResType) or
      not ( Expr^.ResType^.DefType in [cOrdDefinition, cUserOrdDefinition,
        cBooleanDefinition]) then
        begin
          Error( erOrdinalExpressionExpected, Line, Col, '');
          if Assigned( Expr) then
            Dispose( Expr, Done{$IFDEF PPRO}(){$ENDIF});
          Expr := nil;
        end
    else
      if Symbol = csstPred then
        Expr := New( pCodeTree, CreatePred( Expr))
      else
        Expr := New( pCodeTree, CreateSucc( Expr));
    Consume( ctRParen);
    TranslatePredSucc := Expr;
  end;

function tCompiler.TranslateStr: pCodeTree;
  var
    Expr, WidthExpr, DecExpr, StrExpr: pCodeTree;
    FuncName: tNameString;
    Sym: pFunctionSymbol;
  begin
    Consume( ctLParen);
    Expr := ReadExpression( nil);
    if not Assigned( Expr) or not Assigned( Expr^.ResType) then
      Error( erInternalError, Files^.PrevLine, Files^.PrevCol, '');
    if not IsNumeric( Expr^.ResType) then
      Error( erIntegerOrRealExpressionExpected, Files^.PrevLine, Files^.PrevCol, '');
    if LastToken = ctColon then
      begin
        Consume( ctColon);
        WidthExpr := ReadExpression( nil);
        if not Assigned( WidthExpr) or not Assigned( WidthExpr^.ResType) or
          ( WidthExpr^.ResType^.DefType <> cOrdDefinition) or
          ( pOrdDefinition( WidthExpr^.ResType)^.BaseType = cbtChar) then
            Error( erInternalError, Files^.PrevLine, Files^.PrevCol, '');
      end
    else
      WidthExpr := New( pCodeTree, CreateIntConst( 1, LongDef, Files^.PrevLine, Files^.PrevCol));

    case Expr^.ResType^.DefType of
      cOrdDefinition:
        if pOrdDefinition( Expr^.ResType)^.BaseType in
          [cbtShortInt, cbtInteger, cbtLongInt] then
            FuncName := FuncNameSIntToString
        else
          FuncName := FuncNameUIntToString;
      cRealDefinition:
        begin
          FuncName := FuncNameRealToString;
          if LastToken = ctColon then
            begin
              Consume( ctColon);
              DecExpr := ReadExpression( nil);
              if not Assigned( DecExpr) or not Assigned( DecExpr^.ResType) or
                ( DecExpr^.ResType^.DefType <> cOrdDefinition) or
                ( pOrdDefinition( DecExpr^.ResType)^.BaseType = cbtChar) then
                Error( erInternalError, Files^.PrevLine, Files^.PrevCol, '');
            end
          else
            DecExpr := New( pCodeTree, CreateIntConst( -18, LongDef, Files^.PrevLine, Files^.PrevCol));
        end;
    end;
    Sym := pFunctionSymbol( FindWithAlias( FuncName));
    if not Assigned( Sym) or (Sym^._Type <> cFunctionSymbol) then
      Error( erInternalError, Files^.PrevLine, Files^.PrevCol, '');

    Consume( ctComma);
    StrExpr := ReadExpression( StringDef);
    if not Assigned( StrExpr) or not Assigned( StrExpr^.ResType) or
      (StrExpr^.ResType^.DefType <> cStringDefinition) or
      not (StrExpr^.Node.CodeType in [cctVariable, cctLoadValue, cctDeref]) then
        Error( erStringVariableExpected, Files^.PrevLine, Files^.PrevCol, '');
    if Expr^.ResType^.DefType <> cRealDefinition then
      Expr := New( pCodeTree, CreateFunctionCall(
        New( pCodeTree, CreateFunction( Sym, nil)),
        New( pCodeTree, CreateFuncParam(
        New( pCodeTree, CreateFuncParam(
        New( pCodeTree, CreateFuncParam( nil, Expr)),
          New( pCodeTree, CreateLoadAddress( StrExpr, PointerDef)) )),
          WidthExpr)), nil, Files^.PrevLine, Files^.PrevCol ))
    else
      Expr := New( pCodeTree, CreateFunctionCall(
        New( pCodeTree, CreateFunction( Sym, nil)),
        New( pCodeTree, CreateFuncParam(
        New( pCodeTree, CreateFuncParam(
        New( pCodeTree, CreateFuncParam(
        New( pCodeTree, CreateFuncParam( nil, Expr)),
          New( pCodeTree, CreateLoadAddress( StrExpr, PointerDef)) )),
          WidthExpr)),
          DecExpr)), nil, Files^.PrevLine, Files^.PrevCol ));
    Consume( ctRParen);
    TranslateStr := Expr;
  end;

function tCompiler.TranslateIncDec( Symbol: tSystemSymbolType): pCodeTree;
  var
    Expr, Increment: pCodeTree;
    Line, Col: LongInt;
  begin
    Consume( ctLParen);
    Line := Files^.PrevLine;
    Col := Files^.PrevCol;
    Expr := ReadExpression( nil);
    if not Assigned( Expr) or not Assigned( Expr^.ResType) or
      not ( (Expr^.ResType^.DefType in [cOrdDefinition, cUserOrdDefinition,
        cBooleanDefinition]) or ( (Expr^.ResType^.DefType = cPointerDefinition) and
        (pPointerDefinition( Expr^.ResType)^.DefinitionType^.DefType in
          [ cOrdDefinition, cUserOrdDefinition, cBooleanDefinition,
            cPointerDefinition, cArrayDefinition, cRecordDefinition] ) ) ) or
      ( GetParamType( Expr) <> cvtVarParam) then
        begin
          Error( erOrdinalVariableExpected, Line, Col, '');
          if Assigned( Expr) then
            Dispose( Expr, Done{$IFDEF PPRO}(){$ENDIF});
          Expr := nil;
        end
    else
      begin
        Increment := nil;
        if LastToken = ctComma then
          begin
            Consume( ctComma);
            Line := Files^.PrevLine;
            Col := Files^.PrevCol;
            Increment := ReadExpression( LongDef);
            if not Assigned( Increment) or not Assigned( Increment^.ResType) or
               ( Increment^.ResType^.DefType <> cOrdDefinition ) or
               ( pOrdDefinition(Increment^.ResType)^.BaseType = cbtChar ) then
              begin
                Error( erIntegerExpressionExpected, Line, Col, '');
                if Assigned( Increment) then
                  Dispose( Increment, Done{$IFDEF PPRO}(){$ENDIF});
                Increment := nil;
              end
          end;
        if Symbol = csstINC then
          Expr := New( pCodeTree, CreateInc( Expr, Increment, Expr^.ResType))
        else
          Expr := New( pCodeTree, CreateDec( Expr, Increment, Expr^.ResType));
      end;
    Consume( ctRParen);
    TranslateIncDec := Expr;
  end;

function tCompiler.TranslateLength: pCodeTree;
  var
    CodeTree: pCodeTree;
  begin
    Consume( ctLParen);
    CodeTree := ReadExpression( nil);
    if (CodeTree^.ResType^.DefType = cOrdDefinition) and
      (pOrdDefinition(CodeTree^.ResType)^.BaseType = cbtChar) then
      MakeTypeConversion( CodeTree, StringDef)
    else if CodeTree^.ResType^.DefType <> cStringDefinition then
      Error( erStringExpressionExpected, Files^.PrevLine, Files^.PrevCol, '');
    Consume( ctRParen);
    TranslateLength := New( pCodeTree, CreateLength( CodeTree, LongDef));
  end;

function tCompiler.TranslateAssign: pCodeTree;
  var
    F, Name: pCodeTree;
  begin
    Consume( ctLParen);
    F := ReadExpression( nil);
    if not Assigned( F) or not Assigned( F^.ResType) or
      (F^.ResType^.DefType <> cFileDefinition) or
      not (F^.Node.CodeType in [ cctVariable, cctLoadValue]) then
      Error( erFileVariableExpected, Files^.PrevLine, Files^.PrevCol, '');
    Consume( ctComma);
    Name := ReadExpression( StringDef);
    Consume( ctRParen);
    TranslateAssign := New( pCodeTree, CreateAssign( F, Name));
  end;

function tCompiler.TranslateOfs: pCodeTree;
  var
    Expr: pCodeTree;
  begin
    Consume( ctLParen);
    Expr := ReadExpression( nil);
    if not ( Expr^.Node.CodeType in [cctFunction, cctVariable] ) then
      Error( erVariableIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
    Consume( ctRParen);
    TranslateOfs := New( pCodeTree, CreateLoadAddress( Expr, LongDef));
  end;

function tCompiler.ReadNew: pCodeTree;
  var
    CodeTree, ConstructorCode: pCodeTree;
    Symbol: pSymbol;
    ResType: pDefinition;
    L: LongInt;
    FuncName: String;
  begin
    Consume( ctLParen);
    Symbol := nil;
    if LastToken = ctIdentifier then
      Symbol := FindSymbol( LastLine, L);
    if Assigned( Symbol) and (Symbol^._Type = cTypeSymbol) then
      begin
        CodeTree := nil;
        ResType := pTypeSymbol( Symbol)^.Definition;
        if ResType^.DefType <> cPointerDefinition then
          Error( erPointerTypeIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
        if NextToken = ctLParen then
          begin
            Consume( ctLParen);
            CodeTree := ReadExpression( PointerDef);
            MakeTypeConversion( CodeTree, ResType);
            Consume( ctRParen);
          end;
      end
    else
      begin
        CodeTree := ReadExpression( PointerDef);
        ResType := CodeTree^.ResType;
      end;
    if Assigned( CodeTree) and ( GetParamType( CodeTree) <> cvtVarParam ) then
      Error( erVariableIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
    ConstructorCode := nil;
    if (LastToken = ctComma) and
      ( pPointerDefinition( ResType)^.DefinitionType^.DefType = cObjectDefinition) then
      begin
        Consume( ctComma);
        if LastToken <> ctIdentifier then
          Error( erConstructorIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
        FuncName := LastLine;
        Consume( ctIdentifier);
        ConstructorCode := ReadFunctionCall( FuncName,
          New( pCodeTree, CreateLoadValue( nil, nil,
            pPointerDefinition( ResType)^.DefinitionType)), nil );
        if not Assigned( ConstructorCode) or
          not Assigned( ConstructorCode^.Left) or
          (ConstructorCode^.Left^.Node.CodeType <> cctFunction) then
          Error( erInternalError, Files^.PrevLine, Files^.PrevCol, '');
        if ConstructorCode^.Left^.Node.FuncSym^.Definition^.ProcOptions
          and poConstructor = 0 then
          Error( erConstructorIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
      end;
    Consume( ctRParen);
    ReadNew := New( pCodeTree, CreateNewDispose( cctNew, CodeTree,
      ResType, ConstructorCode));
  end;

function tCompiler.ReadDispose: pCodeTree;
  var
    CodeTree: pCodeTree;
    DestructorCode: pCodeTree;
    FuncName: String;
  begin
    Consume( ctLParen);
    CodeTree := ReadExpression( PointerDef);
    if GetParamType( CodeTree) <> cvtVarParam then
      Error( erVariableIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
    DestructorCode := nil;
    if (pPointerDefinition( CodeTree^.ResType)^.DefinitionType^.DefType =
      cObjectDefinition) and (LastToken = ctComma) then
      begin
        Consume( ctComma);
        if LastToken <> ctIdentifier then
          Error( erDestructorIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
        FuncName := LastLine;
        Consume( ctIdentifier);
        DestructorCode := ReadFunctionCall( FuncName,
          New( pCodeTree, CreateLoadValue( nil, nil,
            pPointerDefinition( CodeTree^.ResType)^.DefinitionType)), nil );
        if not Assigned( DestructorCode) or
          not Assigned( DestructorCode^.Left) or
          (DestructorCode^.Left^.Node.CodeType <> cctFunction) then
          Error( erInternalError, Files^.PrevLine, Files^.PrevCol, '');
        if DestructorCode^.Left^.Node.FuncSym^.Definition^.ProcOptions
          and poDestructor = 0 then
          Error( erDestructorIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
      end;
    Consume( ctRParen);
    ReadDispose := New( pCodeTree, CreateNewDispose( cctDispose, CodeTree,
      nil, DestructorCode));
  end;

function tCompiler.TranslateFloat( Symbol: tSystemSymbolType): pCodeTree;
  var
    Expr: pCodeTree;
  begin
    Consume( ctLParen);
    Expr := ReadExpression( ExtendedDef);
    if Expr^.ResType^.DefType = cOrdDefinition then
      MakeTypeConversion( Expr, ExtendedDef);
    Consume( ctRParen);
    TranslateFloat := New( pCodeTree, CreateArithmetic(
      Symbol, Expr, ExtendedDef));
  end;

function tCompiler.TranslateOdd: pCodeTree;
  var
    Expr: pCodeTree;
  begin
    Consume( ctLParen);
    Expr := ReadExpression( LongDef);
    Consume( ctRParen);
    TranslateODD := New( pCodeTree, CreateArithmetic(
      csstODD, Expr, BoolDef));
  end;

function tCompiler.TranslateAbs: pCodeTree;
  var
    Expr: pCodeTree;
  begin
    Consume( ctLParen);
    Expr := ReadExpression( nil);
    if not Assigned( Expr) or not Assigned( Expr^.ResType) then
      Error( erInternalError, Files^.PrevLine, Files^.PrevCol, '');
    if not IsNumeric( Expr^.ResType) then
      Error( erIntegerOrRealExpressionExpected,
        Files^.PrevLine, Files^.PrevCol, '');
    Consume( ctRParen);
    TranslateAbs := New( pCodeTree, CreateArithmetic(
      csstABS, Expr, Expr^.ResType));
  end;

function tCompiler.TranslateAddr: pCodeTree;
  var
    Expr: pCodeTree;
  begin
    Consume( ctLParen);
    Expr := ReadExpression( nil);
    if GetParamType( Expr) <> cvtVarParam then
      Error( erVariableIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
    Consume( ctRParen);
    TranslateAddr := New( pCodeTree, CreateLoadAddress( Expr, PointerDef));
  end;

function tCompiler.TranslateAssigned: pCodeTree;
  var
    Expr: pCodeTree;
  begin
    Consume( ctLParen);
    Expr := ReadExpression( nil);
    if not Assigned( Expr) or not Assigned( Expr^.ResType) then
      Error( erInternalError, Files^.PrevLine, Files^.PrevCol, '');
    if GetParamType( Expr) = cvtParam then
      Error( erVariableIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
    if not (Expr^.ResType^.DefType in [ cPointerDefinition, cFunctionTypeDefinition]) then
      Error( erTypeMismatch, Files^.PrevLine, Files^.PrevCol, '');
    Consume( ctRParen);

    TranslateAssigned := New( pCodeTree, CreateAssigned( Expr, BoolDef));
  end;

function tCompiler.TranslateLow: pCodeTree;
  var
    Def: pDefinition;
    Symbol: pSymbol;
    Expr: pCodeTree;
    L, Val: LongInt;
  begin
    Consume( ctLParen);
    Def := nil;
    Expr := nil;
    if LastToken = ctIdentifier then
      begin
        Symbol := FindSymbol( LastLine, L);
        if Assigned( Symbol) and (Symbol^._Type = cTypeSymbol) then
          begin
            Def := pTypeSymbol( Symbol)^.Definition;
            Consume( ctIdentifier);
          end;
      end;
    if not Assigned( Def) then
      begin
        Expr := ReadExpression( nil);
        Def := Expr^.ResType;
      end;
    if Def^.DefType = cArrayDefinition then
      Def := pArrayDefinition( Def)^.IndexDef;
    case Def^.DefType of
      cOrdDefinition:
        Val := pOrdDefinition( Def)^.Min;
      cStringDefinition,
      cUserOrdDefinition,
      cBooleanDefinition:
        Val := 0;
      else
        Error( erTypeMismatch, Files^.PrevLine, Files^.PrevCol, '');
    end;
    Consume( ctRParen);
    if Assigned( Expr) then
      Dispose( Expr, Done);
    TranslateLow := New( pCodeTree, CreateOrdConst( Val, Def, 0, 0));
  end;

function tCompiler.TranslateHigh: pCodeTree;
  var
    Def: pDefinition;
    Symbol: pSymbol;
    Expr: pCodeTree;
    L, Val: LongInt;
  begin
    Consume( ctLParen);
    Def := nil;
    Expr := nil;
    if LastToken = ctIdentifier then
      begin
        Symbol := FindSymbol( LastLine, L);
        if Assigned( Symbol) and (Symbol^._Type = cTypeSymbol) then
          begin
            Def := pTypeSymbol( Symbol)^.Definition;
            Consume( ctIdentifier);
          end;
      end;
    if not Assigned( Def) then
      begin
        Expr := ReadExpression( nil);
        Def := Expr^.ResType;
      end;
    if Def^.DefType = cArrayDefinition then
      Def := pArrayDefinition( Def)^.IndexDef;
    case Def^.DefType of
      cOrdDefinition:
        Val := pOrdDefinition( Def)^.Max;
      cStringDefinition:
        Val := pStringDefinition( Def)^.Length;
      cUserOrdDefinition:
        Val := pUserOrdDefinition( Def)^.Max;
      cBooleanDefinition:
        Val := 1;
      else
        Error( erTypeMismatch, Files^.PrevLine, Files^.PrevCol, '');
    end;
    Consume( ctRParen);
    if Assigned( Expr) then
      Dispose( Expr, Done);
    TranslateHigh := New( pCodeTree, CreateOrdConst( Val, Def, 0, 0));
  end;

function tCompiler.TranslateConcat: pCodeTree;
  var
   Dest, Source, Expr: pCodeTree;
   pCode: ^pCodeTree;
  begin
    Consume( ctLParen);
    Dest := ReadExpression( StringDef);
    if Dest^.ResType^.DefType <> cStringDefinition then
      MakeTypeConversion( Dest, StringDef);
    Source := nil;
    pCode := @Source;
    while LastToken <> ctRParen do
      begin
        Consume( ctComma);
        Expr := ReadExpression( StringDef);
        if Expr^.ResType^.DefType <> cStringDefinition then
          MakeTypeConversion( Expr, StringDef);
        Expr := New( pCodeTree, CreateLoadAddress( Expr,
          PointerDef));
        pCode^ := New( pCodeTree, CreateFuncParam( pCode^, Expr));
        pCode := @pCode^^.Left;
      end;
    Consume( ctRParen);
    TranslateConcat := New( pCodeTree, CreateConcat( Dest, Source, StringDef));
  end;

function tCompiler.TranslateIncludeExclude( CodeType: tCodeType): pCodeTree;
  var
    Dest, Item: pCodeTree;
  begin
    Consume( ctLParen);
    Dest := ReadExpression( nil);
    if not Assigned( Dest) or not Assigned( Dest^.ResType) then
      Error( erInternalError, Files^.PrevLine, Files^.PrevCol, '');
    if GetParamType( Dest) <> cvtVarParam then
      Error( erVariableIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
    if Dest^.ResType^.DefType <> cSetDefinition then
      Error( erTypeMismatch, Files^.PrevLine, Files^.PrevCol, '');
    Consume( ctComma);
    Item := ReadExpression( nil);
    if not Assigned( Item) or not Assigned( Item^.ResType) then
      Error( erInternalError, Files^.PrevLine, Files^.PrevCol, '');
    if not CompatibleTypes( pSetDefinition( Dest^.ResType)^.SetDef, Item^.ResType) then
      Error( erTypeMismatch, Files^.PrevLine, Files^.PrevCol, '');
    Consume( ctRParen);
    TranslateIncludeExclude := New( pCodeTree, CreateIncludeExclude(
      CodeType, Dest, Item));
  end;

function tCompiler.TranslateMemPort( CodeType: tCodeType;
    ResultType: pDefinition): pCodeTree;
  var
    Expr: pCodeTree;
  begin
    Consume( ctLBracket);
    Expr := ReadExpression( LongDef);
    Consume( ctRBracket);
    TranslateMemPort := New( pCodeTree, CreateMemPort( CodeType, Expr, ResultType));
  end;

function tCompiler.TranslateTypeOf: pCodeTree;
  var
    Symbol: pSymbol;
    L: LongInt;
    CodeTree: pCodeTree;
  begin
    Consume( ctLParen);
    Symbol := nil;
    if LastToken = ctIdentifier then
      Symbol := FindSymbol( LastLine, L);
    if Assigned( Symbol) and (Symbol^._Type = cTypeSymbol) and
      (pTypeSymbol( Symbol)^.Definition^.DefType = cObjectDefinition) then
      begin
        TranslateTypeOf := New( pCodeTree, CreateTypeOfType(
          pObjectDefinition( pTypeSymbol( Symbol)^.Definition), PointerDef));
        NextToken{$IFDEF PPRO}(){$ENDIF};
      end
    else
      begin
        CodeTree := ReadExpression( nil);
        if CodeTree^.ResType^.DefType <> cObjectDefinition then
          Error( erTypeMismatch, Files^.PrevLine, Files^.PrevCol, '');
        TranslateTypeOf := New( pCodeTree,
          CreateTypeOfExpression( CodeTree, PointerDef));
      end;
    Consume( ctRParen);
  end;


function tCompiler.ReadWithStatement: pCodeTree;
  var
    Expression, Block: pCodeTree;
  begin
    Expression := ReadExpression( nil);
    if not ( Expression^.ResType^.DefType in
      [ cRecordDefinition, cObjectDefinition]) or
      (GetParamType( Expression) <> cvtVarParam) then
      Error( erRecordOrObjectVariableExpected, Files^.PrevLine, Files^.PrevCol, '');
    Inc( TempLevel);
    PushTable( Expression^.ResType);
    Expression := New( pCodeTree, CreateLoadAddress( Expression, PointerDef));
    if LastToken = ctComma then
      begin
        Consume( ctComma);
        Block := ReadWithStatement{$IFDEF PPRO}(){$ENDIF};
      end
    else
      begin
        Consume( ctDO);
        Block := nil;
        ReadStatement( Block);
      end;
    PopTable;
    Dec( TempLevel);
    ReadWithStatement := New( pCodeTree, CreateWithBlock( Expression, Block));
  end;


function tCompiler.ReadObjectDefinition( TypeSymbol: pTypeSymbol; SymbolTable: pSymbolTable): pObjectDefinition;
  var
    Definition: pObjectDefinition;
    TpSymbol: pTypeSymbol;
    Base: pObjectDefinition;
    CurSymbols: pSymbolTable;
    L: LongInt;
    OldSymOptions: LongInt;
  begin
    if not (SymbolTable^.SymbolTableType in [ stGlobalTable, stUnitTable]) then
      Error( erLocalObjectTypesAreNotAllowed, Files^.PrevLine, Files^.PrevCol, '');
    Base := nil;
    OldSymOptions := SymbolsOptions;
    SymbolsOptions := csoPublicSymbol;
    if LastToken = ctLParen then
      begin
        Consume( ctLParen);
        if LastToken <> ctIdentifier then
          Error( erTypeIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
        TpSymbol := pTypeSymbol( FindSymbol( LastLine, L));
        if not Assigned( TpSymbol) then
          Error( erUnknownIdentifier, Files^.PrevLine, Files^.PrevCol, LastLine);
        if TpSymbol^._Type <> cTypeSymbol then
          Error( erTypeIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
        if not Assigned( TpSymbol^.Definition) or
          (TpSymbol^.Definition^.DefType <> cObjectDefinition) then
          Error( erObjectTypeExpected, Files^.PrevLine, Files^.PrevCol, '');
        Consume( ctIdentifier);
        Consume( ctRParen);
        Base := pObjectDefinition( TpSymbol^.Definition);
      end;
    Definition := New( pObjectDefinition, Init( Base));
    CurrentObject := Definition;
    TypeSymbol^.Definition := Definition;
    TypeSymbol^.IsOwner := True;
    Definition^.Symbol := TypeSymbol;
    if TypeSymbol = nil then
      Error( erLocalObjectTypesAreNotAllowed, Files^.PrevLine, Files^.PrevCol, '');
    {SymbolTable^.Insert( New( pTypeSymbol,
      Init( ObjectName, Definition, OldSymOptions)) );}

    CurSymbols := Definition^.PublicSymbols;
    while LastToken <> ctEND do
      begin
        case LastToken of
          ctPrivate:
            begin
              NextToken{$IFDEF PPRO}(){$ENDIF};
              SymbolsOptions := csoPrivateSymbol;
            end;
          ctPublic:
            begin
              NextToken{$IFDEF PPRO}(){$ENDIF};
              SymbolsOptions := csoPublicSymbol;
            end;
        end;
        if LastToken = ctIdentifier then
          Inc( CurSymbols^.DataSize, ReadVariables( CurSymbols, cvtField,
            Definition^.GetSize{$IFDEF PPRO}(){$ENDIF}));
        while True do
          begin
            case LastToken of
              ctProcedure,
              ctFunction,
              ctConstructor,
              ctDestructor:
                ReadProcedure( CurSymbols, Definition, True);
              else
                break;
            end;
          end;
        if not (LastToken in [ctPublic, ctPrivate]) then break;
      end;

    Consume( ctEND);
    SymbolsOptions := OldSymOptions;
    {Definition^.Symbol := nil;}
    ReadObjectDefinition := Definition;
    CurrentObject := nil;
  end;


function tCompiler.ReadIfExpression( ResType: pDefinition): pCodeTree;
  var
    Cond, ThenExpr, ElseExpr: pCodeTree;
  begin
    Consume( ctIF);
    Cond := ReadExpression( BoolDef);
    Consume( ctTHEN);
    ThenExpr := ReadExpression( ResType);
    Consume( ctELSE);
    if not Assigned( ResType) then ResType := ThenExpr^.ResType;
    ElseExpr := ReadExpression( ResType);
    ReadIfExpression := New( pCodeTree, CreateIfBlock( Cond, ThenExpr, ElseExpr));
  end;


end.