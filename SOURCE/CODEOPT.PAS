{-----------------------------------------------------------------------}
{    Pascal Pro                                                         }
{       CodeOpt unit                                                    }
{                                              (c) Copyright 1997-1998  }
{                                   Iggor Khachko - hachko@icl.kazan.su }
{-----------------------------------------------------------------------}

{$IFDEF TP}
{$X+,V-,G+,N+,E-,B-,T-}
{$IFDEF DEBUG}
{$I+,S+,R+,C+}
{$ELSE}
{$I-,S-,R-,C-}
{$ENDIF}
{$ENDIF}

unit CodeOpt;

interface

uses Objects, Symbols, Code, PasComp, Compiler, Errors;

type
  pOptomizer = ^tOptomizer;
  tOptomizer = object( tObject)
    Compiler: pCompiler;
    constructor Init( aCompiler: pCompiler);
    procedure OptomizeTree( var CodeTree: pCodeTree);
    procedure DoExpression( var CodeTree: pCodeTree);
    procedure DoAddition( var CodeTree: pCodeTree);
    procedure DoSubtraction( var CodeTree: pCodeTree);
    procedure DoDiv( var CodeTree: pCodeTree);
    procedure DoMod( var CodeTree: pCodeTree);
    procedure DoMultiplication( var CodeTree: pCodeTree);
    procedure DoDivision( var CodeTree: pCodeTree);
    procedure DoNot( var CodeTree: pCodeTree);
    procedure DoNeg( var CodeTree: pCodeTree);
    procedure DoAnd( var CodeTree: pCodeTree);
    procedure DoOr( var CodeTree: pCodeTree);
    procedure DoXor( var CodeTree: pCodeTree);
    procedure DoShr( var CodeTree: pCodeTree);
    procedure DoShl( var CodeTree: pCodeTree);
    procedure DoEqual( var CodeTree: pCodeTree);
    procedure DoUnequal( var CodeTree: pCodeTree);
    procedure DoGreater( var CodeTree: pCodeTree);
    procedure DoLess( var CodeTree: pCodeTree);
    procedure DoGreaterEqual( var CodeTree: pCodeTree);
    procedure DoLessEqual( var CodeTree: pCodeTree);
    procedure DoIN( var CodeTree: pCodeTree);
    procedure DoAssignment( var CodeTree: pCodeTree);
    procedure DoAsn( var CodeTree: pCodeTree);
    procedure DoVariable( var CodeTree: pCodeTree);
    procedure DoLoadValue( var CodeTree: pCodeTree);
    procedure DoAsmBlock( var CodeTree: pCodeTree);
    procedure DoPred( var CodeTree: pCodeTree);
    procedure DoSucc( var CodeTree: pCodeTree);
    procedure DoSetItem( var CodeTree: pCodeTree);
    procedure DoSetRange( var CodeTree: pCodeTree);
    procedure DoLength( var CodeTree: pCodeTree);
    procedure DoArithmeticFunction( var CodeTree: pCodeTree);
    procedure DoFunctionCall( var CodeTree: pCodeTree);
    function FindOperator( PasOp: tPasOperators; var CodeTree: pCodeTree): Boolean;
    procedure DoIfExpression( var CodeTree: pCodeTree);
  end;

procedure MakeTypeConversion( var CodeTree: pCodeTree; Result: pDefinition);

implementation

uses StdLib, IAsm386, Tools;

function GetType( Def: pDefinition): Byte;
  begin
    case Def^.DefType of
      cOrdDefinition:
        case pOrdDefinition(Def)^.BaseType of
          cbtChar, cbtByte, cbtShortInt: GetType := Byte(_8bit);
          cbtWord, cbtInteger: GetType := Byte(_16bit);
          else
            GetType := Byte(_32Bit);
        end;
      cUserOrdDefinition:
        case Def^.GetSize of
          1: GetType := Byte( _8bit);
          2: GetType := Byte( _16bit);
          4: GetType := Byte( _32bit);
        end;
      cRealDefinition:
        GetType := Byte(_Real);
      else
        GetType := 10;
    end
  end;

procedure MakeTypeConversion( var CodeTree: pCodeTree; Result: pDefinition);
  const
    Conv: array [tTypes, tTypes] of tTypeConversion = (
      (ccNoConversion, cc8bit_2_16bit, cc8bit_2_32bit, cc8bit_2_Real),
      (cc16bit_2_8bit, ccNoConversion, cc16bit_2_32bit, cc16bit_2_Real),
      (cc32bit_2_8bit, cc32bit_2_16bit, ccNoConversion, cc32bit_2_Real),
      (ccReal_2_8bit, ccReal_2_16bit, ccReal_2_32bit, ccNoConversion)
  );
  var
    T1, T2: Byte;
    C: pCodeTree;
    TC: pTypedConstSymbol;
    S: String;
  begin
    T1 := GetType( CodeTree^.ResType);
    T2 := GetType( Result);
    if (T1 < 4) and (T2 < 4) then
      begin
        case CodeTree^.Node.CodeType of
          cctIntConst,
          cctCharConst:
            begin
              case Result^.DefType of
                cRealDefinition:
                  begin
                    CodeTree^.Node.CodeType := cctRealConst;
                    CodeTree^.Node.RealValue := CodeTree^.Node.IntValue;
                  end;
                cOrdDefinition:
                  if pOrdDefinition( Result)^.BaseType = cbtChar then
                    begin
                      CodeTree^.Node.CodeType := cctCharConst;
                    end
                  else
                    begin
                      CodeTree^.Node.CodeType := cctIntConst;
                    end;
              end;
              CodeTree^.ResType := Result;
            end;
          cctRealConst:
            begin
              if Result^.DefType = cOrdDefinition then
                begin
                  CodeTree^.Node.CodeType := cctIntConst;
                  CodeTree^.Node.IntValue := Trunc( CodeTree^.Node.RealValue);
                end;
              CodeTree^.ResType := Result;
            end;
          cctOrdConst:
            begin
              if Result^.DefType = cOrdDefinition then
                CodeTree^.Node.CodeType := cctIntConst;
              CodeTree^.ResType := Result;
            end;
          else
            begin
              C := New( pCodeTree, CreateTypeConversion( Conv[tTypes(T1), tTypes(T2)], Result));
              C^.Left := CodeTree;
              CodeTree := C;
            end;
        end;
        Exit;
      end
    else if (Result^.DefType = cStringDefinition) and
      (CodeTree^.ResType^.DefType = cOrdDefinition) and
      ( pOrdDefinition( CodeTree^.ResType)^.BaseType = cbtChar) then
      begin
        if CodeTree^.Node.CodeType = cctCharConst then
          begin
            CodeTree^.Node.CodeType := cctStringConst;
            CodeTree^.Node.StringValue := NewStr( CodeTree^.Node.CharValue);
            CodeTree^.ResType := Result;
            Exit;
          end
        else
          begin
            C := New( pCodeTree, CreateTypeConversion( ccChar_2_String, Result));
            C^.Left := CodeTree;
            CodeTree := C;
            Exit;
          end;
      end
    else if (Result^.DefType = cArrayDefinition) and
      ( (CodeTree^.Node.CodeType = cctStringConst) or
      (CodeTree^.Node.CodeType = cctCharConst) ) then
      begin
        if CodeTree^.Node.CodeType = cctCharConst then
          S := CodeTree^.Node.CharValue
        else
          S := CodeTree^.Node.StringValue^;
        if Length( S) > Result^.GetSize then
          S[ 0] := Chr( Result^.GetSize);
        TC := New( pTypedConstSymbol, Init( CurCompiler^.CreateLabel,
          Result, csoPublicSymbol));
        TC^.Value.ValueType := cvCharArrayValue;
        GetMem( TC^.Value.InfoPtr, Result^.GetSize);
        FillChar( TC^.Value.InfoPtr^, Result^.GetSize, 0);
        Move( S[ 1], TC^.Value.InfoPtr^, Length( S));
        CurCompiler^.GlobalSymbols^.Insert( TC);
        Dispose( CodeTree, Done);
        CodeTree := New( pCodeTree, CreateVariable( TC, 0, 0));
      end
    else
      begin
        {if Assigned( CodeTree^.ResType) and not
          Assigned( CodeTree^.ResType^.Symbol) and
          (CodeTree^.DisposeType and cdtDisposeResult <> 0) then
          Dispose( CodeTree^.ResType, Done);}
        if not Assigned( CodeTree^.ResType) or
          (CodeTree^.ResType^.DefType = cAbstractDefinition) then
          CodeTree^.ResType := Result
        else if (CodeTree^.ResType^.DefType <> Result^.DefType) or
          {(Result^.DefType = cObjectDefinition) or
          ( (Result^.DefType = cPointerDefinition) and
          (pPointerDefinition( Result)^.DefinitionType^.DefType = cObjectDefinition) ) or}
          not SameTypes( Result, CodeTree^.ResType) {or
          not SameTypes( CodeTree^.ResType, Result)} then
          {CodeTree^.ResType := Result;}
          begin
            C := New( pCodeTree, CreateTypeConversion(
              ccUserConversion, Result));
            C^.Left := CodeTree;
            CodeTree := C;
          end;
      end;
  end;

constructor tOptomizer.Init( aCompiler: pCompiler);
  begin
    inherited Init;
    Compiler := aCompiler;
  end;

procedure tOptomizer.OptomizeTree( var CodeTree: pCodeTree);
  var
    Code: ^pCodeTree;
  begin
    Code := @CodeTree;
    while Assigned( Code^) do
      begin
        case Code^^.Node.CodeType of
          cctExpression:
            DoExpression( Code^^.Right);
          cctAsmBlock:
            DoAsmBlock( Code^);
        end;
        Code := @Code^^.Left;
      end;
  end;

procedure tOptomizer.DoExpression( var CodeTree: pCodeTree);
  begin
    if Assigned( CodeTree) then
      begin
        DoExpression( CodeTree^.Left);
        DoExpression( CodeTree^.Right);
        case CodeTree^.Node.CodeType of
          cctAddition: DoAddition( CodeTree);
          cctSubtraction: DoSubtraction( CodeTree);
          cctMultiplication: DoMultiplication( CodeTree);
          cctDivision: DoDivision( CodeTree);
          cctDiv: DoDiv( CodeTree);
          cctMod: DoMod( CodeTree);
          cctNot: DoNot( CodeTree);
          cctNeg: DoNeg( CodeTree);
          cctAnd: DoAnd( CodeTree);
          cctOr: DoOr( CodeTree);
          cctXor: DoXor( CodeTree);
          cctShr: DoShr( CodeTree);
          cctShl: DoShl( CodeTree);
          cctEqual: DoEqual( CodeTree);
          cctUnequal: DoUnequal( CodeTree);
          cctGreater: DoGreater( CodeTree);
          cctLess: DoLess( CodeTree);
          cctGreaterEq: DoGreaterEqual( CodeTree);
          cctLessEq: DoLessEqual( CodeTree);
          cctIN:
            DoIN( CodeTree);
          cctAssignment:
            DoAssignment( CodeTree);
          cctPlusAsn,
          cctMinusAsn,
          cctAndAsn,
          cctOrAsn,
          cctStarAsn,
          cctSlashAsn,
          cctDivAsn,
          cctModAsn,
          cctShlAsn,
          cctShrAsn,
          cctXorAsn:
            DoAsn( CodeTree);
          cctVariable: DoVariable( CodeTree);
          cctPred:
            DoPred( CodeTree);
          cctSucc:
            DoSucc( CodeTree);
          cctSetItem:
            DoSetItem( CodeTree);
          cctSetRange:
            DoSetRange( CodeTree);
          cctLength:
            DoLength( CodeTree);
          cctArithmeticFunction:
            DoArithmeticFunction( CodeTree);
          cctFunctionCall:
            DoFunctionCall( CodeTree);
          cctIfBlock:
            DoIfExpression( CodeTree);
        end;
      end;
  end;

procedure tOptomizer.DoAddition( var CodeTree: pCodeTree);
  var
    S: String;
    Tree: pCodeTree;
  begin
    with Compiler^ do
    begin
      if not Assigned( CodeTree^.Left) or not Assigned( CodeTree^.Right) then
        Exit;
      if (CodeTree^.Left^.Node.CodeType in [cctCharConst, cctStringConst]) and
        (CodeTree^.Right^.Node.CodeType in [cctCharConst, cctStringConst]) then
       begin
        if CodeTree^.Left^.Node.CodeType = cctCharConst then
          begin
            S := CodeTree^.Left^.Node.CharValue;
          end
        else
          begin
            S := CodeTree^.Left^.Node.StringValue^;
            {DisposeStr( Left^.Node.StringValue);}
          end;
        if CodeTree^.Right^.Node.CodeType = cctCharConst then
          begin
            S := S + CodeTree^.Right^.Node.CharValue;
          end
        else
          begin
            S := S + CodeTree^.Right^.Node.StringValue^;
            {DisposeStr( Right^.Node.StringValue);}
          end;
        CodeTree^.Node.StringValue := NewStr( S);
        CodeTree^.Node.CodeType := cctStringConst;
        Dispose( CodeTree^.Left, Done);
        Dispose( CodeTree^.Right, Done);
        CodeTree^.Left := nil;
        CodeTree^.Right := nil;
        CodeTree^.ResType := StringDef;
        Exit;
      end;
    if (CodeTree^.Left^.Node.CodeType = cctIntConst) then
      begin
        if (CodeTree^.Right^.Node.CodeType = cctIntConst) then
          begin
            CodeTree^.Node.IntValue := CodeTree^.Left^.Node.IntValue +
              CodeTree^.Right^.Node.IntValue;
            CodeTree^.Node.CodeType := cctIntConst;
            Dispose( CodeTree^.Left, Done);
            Dispose( CodeTree^.Right, Done);
            CodeTree^.ResType := LongDef;
            CodeTree^.Left := nil;
            CodeTree^.Right := nil;
            Exit;
          end
        else if (CodeTree^.Right^.Node.CodeType = cctRealConst) then
          begin
            CodeTree^.Node.RealValue := CodeTree^.Left^.Node.IntValue +
              CodeTree^.Right^.Node.RealValue;
            CodeTree^.Node.CodeType := cctRealConst;
            Dispose( CodeTree^.Left, Done);
            Dispose( CodeTree^.Right, Done);
            CodeTree^.Left := nil;
            CodeTree^.Right := nil;
            CodeTree^.ResType := ExtendedDef;
            Exit;
          end;
        end
      else if (CodeTree^.Left^.Node.CodeType = cctRealConst) then
        begin
          if (CodeTree^.Right^.Node.CodeType = cctIntConst) then
            begin
              CodeTree^.Node.RealValue := CodeTree^.Left^.Node.RealValue +
                CodeTree^.Right^.Node.IntValue;
              CodeTree^.Node.CodeType := cctRealConst;
              Dispose( CodeTree^.Left, Done);
              Dispose( CodeTree^.Right, Done);
              CodeTree^.Left := nil;
              CodeTree^.Right := nil;
              CodeTree^.ResType := ExtendedDef;
              Exit;
            end
          else if (CodeTree^.Right^.Node.CodeType = cctRealConst) then
            begin
              CodeTree^.Node.RealValue := CodeTree^.Left^.Node.RealValue +
                CodeTree^.Right^.Node.RealValue;
              CodeTree^.Node.CodeType := cctRealConst;
              Dispose( CodeTree^.Left, Done);
              Dispose( CodeTree^.Right, Done);
              CodeTree^.Left := nil;
              CodeTree^.Right := nil;
              CodeTree^.ResType := ExtendedDef;
              Exit;
            end;
        end
      else if CodeTree^.Left^.Node.CodeType = cctSetConst then
        begin
          if (CodeTree^.Right^.Node.CodeType = cctSetConst) and
            CompatibleTypes( CodeTree^.Left^.ResType, CodeTree^.Right^.ResType) then
            begin
              Tree := New( pCodeTree, CreateSetConst(
                CodeTree^.Left^.Node.SetValue^ + CodeTree^.Right^.Node.SetValue^,
                CodeTree^.Left^.ResType,
                CodeTree^.Left^.Line, CodeTree^.Left^.Col));
              Tree^.DisposeType := CodeTree^.Left^.DisposeType;
              CodeTree^.Left^.DisposeType := CodeTree^.Left^.DisposeType and not cdtDisposeResult;
              Dispose( CodeTree, Done);
              CodeTree := Tree;
              Exit;
            end;
        end;

      if FindOperator( cpoPlus, CodeTree) then
        Exit;

      if not IsNumeric( CodeTree^.Left^.ResType) or not IsNumeric( CodeTree^.Right^.ResType) then
        begin
          case CodeTree^.Left^.ResType^.DefType of
            cPointerDefinition:
              if (CodeTree^.Right^.ResType^.DefType = cOrdDefinition) and
                (pOrdDefinition( CodeTree^.Right^.ResType)^.BaseType <> cbtChar) and
                (pPointerDefinition( CodeTree^.Left^.ResType)^.DefinitionType^.DefType in
                  [cPointerDefinition, cOrdDefinition, cUserOrdDefinition,
                    cBooleanDefinition, cRecordDefinition, cArrayDefinition]) then
              begin
                if CodeTree^.Right^.ResType^.GetSize < 4 then
                  MakeTypeConversion( CodeTree^.Right, LongDef);
                CodeTree^.ResType := CodeTree^.Left^.ResType;
                Exit;
              end;
            cSetDefinition:
              begin
                if CompatibleTypes( CodeTree^.Left^.ResType,
                  CodeTree^.Right^.ResType) then
                  begin
                    if not Assigned( CodeTree^.ResType) then
                      CodeTree^.ResType := New( pSetDefinition, Init(
                        pSetDefinition( CodeTree^.Left^.ResType)^.SetDef));
                    Exit;
                  end;
              end;
            cStringDefinition,
            cOrdDefinition:
              if CodeTree^.Right^.ResType^.DefType in
                [ cStringDefinition, cOrdDefinition] then
                begin
                  if CodeTree^.Left^.ResType^.DefType = cOrdDefinition then
                    MakeTypeConversion( CodeTree^.Left, StringDef);
                  if CodeTree^.Right^.ResType^.DefType = cOrdDefinition then
                    MakeTypeConversion( CodeTree^.Right, StringDef);
                  CodeTree^.ResType := StringDef;
                  Exit;
                end;
          end;
        end
      else
        begin
        if CodeTree^.Left^.ResType = CodeTree^.Right^.ResType then
          CodeTree^.ResType := CodeTree^.Left^.ResType
        else
          begin
            if (CodeTree^.Left^.ResType^.DefType = cRealDefinition) or
              (CodeTree^.Right^.ResType^.DefType = cRealDefinition) then
              begin
                CodeTree^.ResType := ExtendedDef;
                MakeTypeConversion( CodeTree^.Left, CodeTree^.ResType);
                MakeTypeConversion( CodeTree^.Right, CodeTree^.ResType);
              end
            else
              begin
                if CodeTree^.Left^.Node.CodeType = cctIntConst then
                  begin
                    CodeTree^.ResType := CodeTree^.Right^.ResType;
                    CodeTree^.Left^.ResType := CodeTree^.ResType;
                  end
                else if CodeTree^.Right^.Node.CodeType = cctIntConst then
                  begin
                    CodeTree^.ResType := CodeTree^.Left^.ResType;
                    CodeTree^.Right^.ResType := CodeTree^.ResType;
                  end
                else if CodeTree^.Left^.ResType^.GetSize < CodeTree^.Right^.ResType^.GetSize then
                  begin
                    CodeTree^.ResType := CodeTree^.Right^.ResType;
                    MakeTypeConversion( CodeTree^.Left, CodeTree^.ResType)
                  end
                else
                  begin
                    CodeTree^.ResType := CodeTree^.Left^.ResType;
                    if CodeTree^.Right^.Node.CodeType <> cctIntConst then
                      MakeTypeConversion( CodeTree^.Right, CodeTree^.ResType)
                    else
                      CodeTree^.Left^.ResType := CodeTree^.ResType;
                  end;
              end;
          end;
          Exit;
        end;
      end;
    Compiler^.Error( erCannotFindThisOperator, CodeTree^.Line, CodeTree^.Col, '');
  end;

procedure tOptomizer.DoSubtraction( var CodeTree: pCodeTree);
  var
    Tree: pCodeTree;
  begin
    with Compiler^, CodeTree^ do
      begin
        if not Assigned( Left) or not Assigned( Right) then
          Exit;
        if (Left^.Node.CodeType = cctIntConst) then
          begin
            if (Right^.Node.CodeType = cctIntConst) then
              begin
                Node.IntValue := Left^.Node.IntValue - Right^.Node.IntValue;
                Node.CodeType := cctIntConst;
{$IFDEF TP}
                Dispose( Left, Done);
                Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                Dispose( Left, Done());
                Dispose( Right, Done());
{$ENDIF}
                ResType := LongDef;
                Left := nil;
                Right := nil;
                Exit;
              end
            else if (Right^.Node.CodeType = cctRealConst) then
              begin
                Node.RealValue := Left^.Node.IntValue - Right^.Node.RealValue;
                Node.CodeType := cctRealConst;
{$IFDEF TP}
                Dispose( Left, Done);
                Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                Dispose( Left, Done());
                Dispose( Right, Done());
{$ENDIF}
                Left := nil;
                Right := nil;
                ResType := ExtendedDef;
                Exit;
              end;
          end
        else if (Left^.Node.CodeType = cctRealConst) then
          begin
            if (Right^.Node.CodeType = cctIntConst) then
              begin
                Node.RealValue := Left^.Node.RealValue - Right^.Node.IntValue;
                Node.CodeType := cctRealConst;
{$IFDEF TP}
                Dispose( Left, Done);
                Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                Dispose( Left, Done());
                Dispose( Right, Done());
{$ENDIF}
                Left := nil;
                Right := nil;
                ResType := ExtendedDef;
                Exit;
              end
            else if (Right^.Node.CodeType = cctRealConst) then
              begin
                Node.RealValue := Left^.Node.RealValue - Right^.Node.RealValue;
                Node.CodeType := cctRealConst;
{$IFDEF TP}
                Dispose( Left, Done);
                Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                Dispose( Left, Done());
                Dispose( Right, Done());
{$ENDIF}
                Left := nil;
                Right := nil;
                ResType := ExtendedDef;
                Exit;
              end;
          end
        else if CodeTree^.Left^.Node.CodeType = cctSetConst then
          begin
            if (CodeTree^.Right^.Node.CodeType = cctSetConst) and
              CompatibleTypes( CodeTree^.Left^.ResType, CodeTree^.Right^.ResType) then
              begin
                Tree := New( pCodeTree, CreateSetConst(
                  CodeTree^.Left^.Node.SetValue^ - CodeTree^.Right^.Node.SetValue^,
                  CodeTree^.Left^.ResType,
                  CodeTree^.Left^.Line, CodeTree^.Left^.Col));
                Tree^.DisposeType := CodeTree^.Left^.DisposeType;
                CodeTree^.Left^.DisposeType := CodeTree^.Left^.DisposeType and not cdtDisposeResult;
{$IFDEF TP}
                Dispose( CodeTree, Done);
{$ENDIF}
{$IFDEF PPRO}
                Dispose( CodeTree, Done());
{$ENDIF}
                CodeTree := Tree;
                Exit;
              end;
          end;

        {operator overaloading }

      if not IsNumeric( CodeTree^.Left^.ResType) or not IsNumeric( CodeTree^.Right^.ResType) then
        begin
          case CodeTree^.Left^.ResType^.DefType of
            cPointerDefinition:
              if (CodeTree^.Right^.ResType^.DefType = cOrdDefinition) and
                (pOrdDefinition( CodeTree^.Right^.ResType)^.BaseType <> cbtChar) and
                (pPointerDefinition( CodeTree^.Left^.ResType)^.DefinitionType^.DefType in
                  [cPointerDefinition, cOrdDefinition, cUserOrdDefinition,
                    cBooleanDefinition, cRecordDefinition, cArrayDefinition]) then
              begin
                if CodeTree^.Right^.ResType^.GetSize < 4 then
                  MakeTypeConversion( CodeTree^.Right, LongDef);
                CodeTree^.ResType := CodeTree^.Left^.ResType;
                Exit;
              end;
            cSetDefinition:
            begin
              if CompatibleTypes( CodeTree^.Left^.ResType,
                CodeTree^.Right^.ResType) then
                begin
                  if not Assigned( CodeTree^.ResType) then
                    begin
                      CodeTree^.ResType := New( pSetDefinition, Init(
                        pSetDefinition( CodeTree^.Left^.ResType)^.SetDef));
                      CodeTree^.DisposeType :=
                        CodeTree^.DisposeType or cdtDisposeResult;
                    end;
                  Exit;
                end;
            end;
          end;
        end
      else
        begin
        if CodeTree^.Left^.ResType = CodeTree^.Right^.ResType then
          CodeTree^.ResType := CodeTree^.Left^.ResType
        else
          begin
            if (CodeTree^.Left^.ResType^.DefType = cRealDefinition) or
              (CodeTree^.Right^.ResType^.DefType = cRealDefinition) then
              begin
                CodeTree^.ResType := ExtendedDef;
                MakeTypeConversion( CodeTree^.Left, CodeTree^.ResType);
                MakeTypeConversion( CodeTree^.Right, CodeTree^.ResType);
              end
            else
              begin
                if CodeTree^.Left^.Node.CodeType = cctIntConst then
                  begin
                    CodeTree^.ResType := CodeTree^.Right^.ResType;
                    CodeTree^.Left^.ResType := CodeTree^.ResType;
                  end
                else if CodeTree^.Right^.Node.CodeType = cctIntConst then
                  begin
                    CodeTree^.ResType := CodeTree^.Left^.ResType;
                    CodeTree^.Right^.ResType := CodeTree^.ResType;
                  end
{$IFDEF TP}
                else if CodeTree^.Left^.ResType^.GetSize < CodeTree^.Right^.ResType^.GetSize then
{$ENDIF}
{$IFDEF PPRO}
                else if CodeTree^.Left^.ResType^.GetSize() < CodeTree^.Right^.ResType^.GetSize() then
{$ENDIF}
                  begin
                    CodeTree^.ResType := CodeTree^.Right^.ResType;
                    MakeTypeConversion( CodeTree^.Left, CodeTree^.ResType)
                  end
                else
                  begin
                    CodeTree^.ResType := CodeTree^.Left^.ResType;
                    if CodeTree^.Right^.Node.CodeType <> cctIntConst then
                      MakeTypeConversion( CodeTree^.Right, CodeTree^.ResType)
                    else
                      CodeTree^.Left^.ResType := CodeTree^.ResType;
                  end;
              end;
          end;
          Exit;
        end;
      end;
    Compiler^.Error( erCannotFindThisOperator, CodeTree^.Line, CodeTree^.Col, '');
  end;

procedure tOptomizer.DoDiv( var CodeTree: pCodeTree);
  begin
    with Compiler^, CodeTree^ do
      begin
        if not Assigned( Left) or not Assigned( Right) then
          Exit;
        if (Left^.Node.CodeType = cctIntConst) and
          (Right^.Node.CodeType = cctIntConst) then
          begin
            Node.CodeType := cctIntConst;
            Node.IntValue := Left^.Node.IntValue div Right^.Node.IntValue;
{$IFDEF TP}
            Dispose( Left, Done);
            Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
            Dispose( Left, Done());
            Dispose( Right, Done());
{$ENDIF}
            ResType := LongDef;
            Left := nil;
            Right := nil;
            Exit;
          end;
        {operator overaloading}
        if FindOperator( cpoDiv, CodeTree) then
          Exit;
        if not IsNumeric( Left^.ResType) or not IsNumeric( Right^.ResType) then
          Error( erCannotFindThisOperator, Line, Col, '');
        if Left^.ResType = Right^.ResType then
          ResType := Left^.ResType
        else
          begin
            if Left^.Node.CodeType = cctIntConst then
              begin
                ResType := Right^.ResType;
                Left^.ResType := ResType;
              end
            else if Right^.Node.CodeType = cctIntConst then
                  begin
                    ResType := Left^.ResType;
                    Right^.ResType := ResType;
                  end
{$IFDEF TP}
            else if Left^.ResType^.GetSize < Right^.ResType^.GetSize then
{$ENDIF}
{$IFDEF PPRO}
            else if Left^.ResType^.GetSize() < Right^.ResType^.GetSize() then
{$ENDIF}
                  begin
                    ResType := Right^.ResType;
                    MakeTypeConversion( Left, ResType)
                  end
            else
              begin
                    ResType := Left^.ResType;
                    if Right^.Node.CodeType <> cctIntConst then
                      MakeTypeConversion( Right, ResType)
                    else
                      Left^.ResType := ResType;
              end;
          end;
      end;
  end;

procedure tOptomizer.DoMod( var CodeTree: pCodeTree);
  begin
    with Compiler^, CodeTree^ do
      begin
        if not Assigned( Left) or not Assigned( Right) then
          Exit;
        if (Left^.Node.CodeType = cctIntConst) and
          (Right^.Node.CodeType = cctIntConst) then
          begin
            Node.CodeType := cctIntConst;
            Node.IntValue := Left^.Node.IntValue mod Right^.Node.IntValue;
{$IFDEF TP}
            Dispose( Left, Done);
            Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
            Dispose( Left, Done());
            Dispose( Right, Done());
{$ENDIF}
            ResType := LongDef;
            Left := nil;
            Right := nil;
            Exit;
          end;
        {operator overaloading}
        if FindOperator( cpoMod, CodeTree) then
          Exit;
        if not IsNumeric( Left^.ResType) or not IsNumeric( Right^.ResType) then
          Error( erCannotFindThisOperator, Line, Col, '');
        if Left^.ResType = Right^.ResType then
          ResType := Left^.ResType
        else
          begin
            if Left^.Node.CodeType = cctIntConst then
              begin
                ResType := Right^.ResType;
                Left^.ResType := ResType;
              end
            else if Right^.Node.CodeType = cctIntConst then
                  begin
                    ResType := Left^.ResType;
                    Right^.ResType := ResType;
                  end
{$IFDEF TP}
            else if Left^.ResType^.GetSize < Right^.ResType^.GetSize then
{$ENDIF}
{$IFDEF PPRO}
            else if Left^.ResType^.GetSize() < Right^.ResType^.GetSize() then
{$ENDIF}
                  begin
                    ResType := Right^.ResType;
                    MakeTypeConversion( Left, ResType)
                  end
            else
              begin
                    ResType := Left^.ResType;
                    if Right^.Node.CodeType <> cctIntConst then
                      MakeTypeConversion( Right, ResType)
                    else
                      Left^.ResType := ResType;
              end;
          end;
      end;
  end;

procedure tOptomizer.DoMultiplication( var CodeTree: pCodeTree);
  var
    Tree: pCodeTree;
  begin
    with Compiler^, CodeTree^ do
      begin
        if not Assigned( Left) or not Assigned( Right) then
          Exit;
        if (Left^.Node.CodeType = cctIntConst) then
          begin
            if (Right^.Node.CodeType = cctIntConst) then
              begin
                Node.IntValue := Left^.Node.IntValue * Right^.Node.IntValue;
                Node.CodeType := cctIntConst;
                ResType := LongDef;
{$IFDEF TP}
                Dispose( Left, Done);
                Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                Dispose( Left, Done());
                Dispose( Right, Done());
{$ENDIF}
                Left := nil;
                Right := nil;
                Exit;
              end
            else if (Right^.Node.CodeType = cctRealConst) then
              begin
                Node.RealValue := Left^.Node.IntValue * Right^.Node.RealValue;
                Node.CodeType := cctRealConst;
{$IFDEF TP}
                Dispose( Left, Done);
                Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                Dispose( Left, Done());
                Dispose( Right, Done());
{$ENDIF}
                Left := nil;
                Right := nil;
                ResType := ExtendedDef;
                Exit;
              end;
          end
        else if (Left^.Node.CodeType = cctRealConst) then
          begin
            if (Right^.Node.CodeType = cctIntConst) then
              begin
                Node.RealValue := Left^.Node.RealValue * Right^.Node.IntValue;
                Node.CodeType := cctRealConst;
{$IFDEF TP}
                Dispose( Left, Done);
                Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                Dispose( Left, Done());
                Dispose( Right, Done());
{$ENDIF}
                Left := nil;
                Right := nil;
                ResType := ExtendedDef;
                Exit;
              end
            else if (Right^.Node.CodeType = cctRealConst) then
              begin
                Node.RealValue := Left^.Node.RealValue * Right^.Node.RealValue;
                Node.CodeType := cctRealConst;
{$IFDEF TP}
                Dispose( Left, Done);
                Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                Dispose( Left, Done());
                Dispose( Right, Done());
{$ENDIF}
                Left := nil;
                Right := nil;
                ResType := ExtendedDef;
                Exit;
              end;
          end
        else if CodeTree^.Left^.Node.CodeType = cctSetConst then
          begin
            if (CodeTree^.Left^.Node.CodeType = cctSetConst) and
              CompatibleTypes( CodeTree^.Left^.ResType, CodeTree^.Right^.ResType) then
              begin
                Tree := New( pCodeTree, CreateSetConst(
                  CodeTree^.Left^.Node.SetValue^ * CodeTree^.Right^.Node.SetValue^,
                  CodeTree^.Left^.ResType,
                  CodeTree^.Left^.Line, CodeTree^.Left^.Col));
                Tree^.DisposeType := CodeTree^.Left^.DisposeType;
                CodeTree^.Left^.DisposeType := CodeTree^.Left^.DisposeType and not cdtDisposeResult;
{$IFDEF TP}
                Dispose( CodeTree, Done);
{$ENDIF}
{$IFDEF PPRO}
                Dispose( CodeTree, Done());
{$ENDIF}
                CodeTree := Tree;
                Exit;
              end;
          end;

        {operator overaloading}
      if FindOperator( cpoStar, CodeTree) then
          Exit;

      if not IsNumeric( CodeTree^.Left^.ResType) or not IsNumeric( CodeTree^.Right^.ResType) then
        begin
          if CodeTree^.Left^.ResType^.DefType = cSetDefinition then
            begin
              if CompatibleTypes( CodeTree^.Left^.ResType,
                CodeTree^.Right^.ResType) then
                begin
                  if not Assigned( CodeTree^.ResType) then
                    begin
                      CodeTree^.ResType := New( pSetDefinition, Init(
                        pSetDefinition( CodeTree^.Left^.ResType)^.SetDef));
                      CodeTree^.DisposeType :=
                        CodeTree^.DisposeType or cdtDisposeResult;
                    end;
                  Exit;
                end;
            end;
        end
      else
        begin
        if CodeTree^.Left^.ResType = CodeTree^.Right^.ResType then
          CodeTree^.ResType := CodeTree^.Left^.ResType
        else
          begin
            if (CodeTree^.Left^.ResType^.DefType = cRealDefinition) or
              (CodeTree^.Right^.ResType^.DefType = cRealDefinition) then
              begin
                CodeTree^.ResType := Compiler^.ExtendedDef;
                MakeTypeConversion( CodeTree^.Left, CodeTree^.ResType);
                MakeTypeConversion( CodeTree^.Right, CodeTree^.ResType);
              end
            else
              begin
                if CodeTree^.Left^.Node.CodeType = cctIntConst then
                  begin
                    CodeTree^.ResType := CodeTree^.Right^.ResType;
                    CodeTree^.Left^.ResType := CodeTree^.ResType;
                  end
                else if CodeTree^.Right^.Node.CodeType = cctIntConst then
                  begin
                    CodeTree^.ResType := CodeTree^.Left^.ResType;
                    CodeTree^.Right^.ResType := CodeTree^.ResType;
                  end
{$IFDEF TP}
                else if CodeTree^.Left^.ResType^.GetSize < CodeTree^.Right^.ResType^.GetSize then
{$ENDIF}
{$IFDEF PPRO}
                else if CodeTree^.Left^.ResType^.GetSize() < CodeTree^.Right^.ResType^.GetSize() then
{$ENDIF}
                  begin
                    CodeTree^.ResType := CodeTree^.Right^.ResType;
                    MakeTypeConversion( CodeTree^.Left, CodeTree^.ResType)
                  end
                else
                  begin
                    CodeTree^.ResType := CodeTree^.Left^.ResType;
                    if CodeTree^.Right^.Node.CodeType <> cctIntConst then
                      MakeTypeConversion( CodeTree^.Right, CodeTree^.ResType)
                    else
                      CodeTree^.Left^.ResType := CodeTree^.ResType;
                  end;
              end;
          end;
          Exit;
        end;
      end;
    Compiler^.Error( erCannotFindThisOperator, CodeTree^.Line, CodeTree^.Col, '');
  end;

procedure tOptomizer.DoDivision( var CodeTree: pCodeTree);
  begin
    with Compiler^, CodeTree^ do
      begin
        if not Assigned( Left) or not Assigned( Right) then
          Exit;
        if (Left^.Node.CodeType = cctIntConst) then
          begin
            if (Right^.Node.CodeType = cctIntConst) then
              begin
                Node.RealValue := Left^.Node.IntValue / Right^.Node.IntValue;
                Node.CodeType := cctRealConst;
                ResType := ExtendedDef;
{$IFDEF TP}
                Dispose( Left, Done);
                Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                Dispose( Left, Done());
                Dispose( Right, Done());
{$ENDIF}
                Left := nil;
                Right := nil;
                Exit;
              end
            else if (Right^.Node.CodeType = cctRealConst) then
              begin
                Node.RealValue := Left^.Node.IntValue / Right^.Node.RealValue;
                Node.CodeType := cctRealConst;
{$IFDEF TP}
                Dispose( Left, Done);
                Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                Dispose( Left, Done());
                Dispose( Right, Done());
{$ENDIF}
                Left := nil;
                Right := nil;
                ResType := ExtendedDef;
                Exit;
              end;
          end
        else if (Left^.Node.CodeType = cctRealConst) then
          begin
            if (Right^.Node.CodeType = cctIntConst) then
              begin
                Node.RealValue := Left^.Node.RealValue / Right^.Node.IntValue;
                Node.CodeType := cctRealConst;
{$IFDEF TP}
                Dispose( Left, Done);
                Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                Dispose( Left, Done());
                Dispose( Right, Done());
{$ENDIF}
                Left := nil;
                Right := nil;
                ResType := ExtendedDef;
                Exit;
              end
            else if (Right^.Node.CodeType = cctRealConst) then
              begin
                Node.RealValue := Left^.Node.RealValue / Right^.Node.RealValue;
                Node.CodeType := cctRealConst;
{$IFDEF TP}
                Dispose( Left, Done);
                Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                Dispose( Left, Done());
                Dispose( Right, Done());
{$ENDIF}
                Left := nil;
                Right := nil;
                ResType := ExtendedDef;
                Exit;
              end;
          end;

        if FindOperator( cpoSlash, CodeTree) then
          Exit;

        if IsNumeric( CodeTree^.Left^.ResType) and
          IsNumeric( CodeTree^.Right^.ResType) then
          begin
            if CodeTree^.Left^.ResType^.DefType = cOrdDefinition then
              MakeTypeConversion( CodeTree^.Left, ExtendedDef);
            if CodeTree^.Right^.ResType^.DefType = cOrdDefinition then
              MakeTypeConversion( CodeTree^.Right, ExtendedDef);
            CodeTree^.ResType := ExtendedDef;
            Exit;
          end;
        Error( erCannotFindThisOperator, CodeTree^.Line, CodeTree^.Col, '');
      end;
  end;

procedure tOptomizer.DoNot( var CodeTree: pCodeTree);
  begin
    with Compiler^, CodeTree^ do
      begin
        case Left^.Node.CodeType of
          cctBoolConst:
            begin
              Node.BoolValue := not Left^.Node.BoolValue;
              Node.CodeType := cctBoolConst;
              ResType := BoolDef;
{$IFDEF TP}
              Dispose( Left, Done);
{$ENDIF}
{$IFDEF PPRO}
              Dispose( Left, Done());
{$ENDIF}
              Left := nil;
              Exit;
            end;
          cctIntConst:
            begin
              Node.IntValue := not Left^.Node.IntValue;
              Node.CodeType := cctIntConst;
              ResType := LongDef;
{$IFDEF TP}
              Dispose( Left, Done);
{$ENDIF}
{$IFDEF PPRO}
              Dispose( Left, Done());
{$ENDIF}
              Left := nil;
              Exit;
            end;
        end;

        if FindOperator( cpoNot, CodeTree) then
          Exit;
        if (Left^.ResType^.DefType = cBooleanDefinition) then
          begin
            ResType := Left^.ResType;
            Exit;
          end
        else if (Left^.ResType^.DefType = cOrdDefinition) and
          (pOrdDefinition(Left^.ResType)^.BaseType <> cbtChar) then
          begin
            ResType := Left^.ResType;
            Exit;
          end;
        Error( erCannotFindThisOperator, CodeTree^.Line, CodeTree^.Col, '');
      end;
  end;

procedure tOptomizer.DoNeg( var CodeTree: pCodeTree);
  begin
    with Compiler^, CodeTree^ do
      begin
        case Left^.Node.CodeType of
          cctIntConst:
            begin
              Node.IntValue := -Left^.Node.IntValue;
              Node.CodeType := cctIntConst;
              ResType := LongDef;
{$IFDEF TP}
              Dispose( Left, Done);
{$ENDIF}
{$IFDEF PPRO}
              Dispose( Left, Done());
{$ENDIF}
              Left := nil;
              Exit;
            end;
          cctRealConst:
            begin
              Node.RealValue := -Left^.Node.RealValue;
              Node.CodeType := cctRealConst;
              ResType := ExtendedDef;
{$IFDEF TP}
              Dispose( Left, Done);
{$ENDIF}
{$IFDEF PPRO}
              Dispose( Left, Done());
{$ENDIF}
              Left := nil;
              Exit;
            end;
        end;

        if FindOperator( cpoMinus, CodeTree) then
          Exit;
        if IsNumeric( CodeTree^.Left^.ResType) then
          begin
            ResType := Left^.ResType;
            Exit;
          end;
        Error( erCannotFindThisOperator, CodeTree^.Line, CodeTree^.Col, '');
      end;
  end;

procedure tOptomizer.DoAnd( var CodeTree: pCodeTree);
  begin
    with Compiler^, CodeTree^ do
      begin
        if Left^.Node.CodeType = Right^.Node.CodeType then
          begin
            if Left^.Node.CodeType = cctBoolConst then
              begin
                Node.BoolValue := Left^.Node.BoolValue and Right^.Node.BoolValue;
                Node.CodeType := cctBoolConst;
                ResType := BoolDef;
{$IFDEF TP}
                Dispose( Left, Done);
                Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                Dispose( Left, Done());
                Dispose( Right, Done());
{$ENDIF}
                Left := nil;
                Right := nil;
                Exit;
              end
            else if Left^.Node.CodeType = cctIntConst then
              begin
                Node.IntValue := Left^.Node.IntValue and Right^.Node.IntValue;
                Node.CodeType := cctIntConst;
                ResType := LongDef;
{$IFDEF TP}
                Dispose( Left, Done);
                Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                Dispose( Left, Done());
                Dispose( Right, Done());
{$ENDIF}
                Left := nil;
                Right := nil;
                Exit;
              end;
          end;

        if FindOperator( cpoAnd, CodeTree) then
          Exit;
        if (Left^.ResType^.DefType = cBooleanDefinition) and
          (Right^.ResType^.DefType = cBooleanDefinition) then
          begin
            ResType := Left^.ResType;
            Exit;
          end
        else if (Left^.ResType^.DefType = cOrdDefinition) and
          (Right^.ResType^.DefType = cOrdDefinition) and
          (pOrdDefinition(Left^.ResType)^.BaseType <> cbtChar) and
          (pOrdDefinition(Right^.ResType)^.BaseType <> cbtChar) then
          begin
{$IFDEF TP}
            if (Left^.ResType^.GetSize = Right^.ResType^.GetSize) then
{$ENDIF}
{$IFDEF PPRO}
            if (Left^.ResType^.GetSize() = Right^.ResType^.GetSize()) then
{$ENDIF}
              begin
                ResType := Left^.ResType;
                Exit;
              end
{$IFDEF TP}
            else if (Right^.Node.CodeType = cctIntConst) or
              ( ( Left^.Node.CodeType<> cctIntConst) and
              (Right^.ResType^.GetSize < Left^.ResType^.GetSize) ) then
{$ENDIF}
{$IFDEF PPRO}
            else if (Right^.Node.CodeType = cctIntConst) or
              ( ( Left^.Node.CodeType<> cctIntConst) and
              (Right^.ResType^.GetSize() < Left^.ResType^.GetSize()) ) then
{$ENDIF}
              begin
                ResType := Left^.ResType;
                MakeTypeConversion( Right, ResType);
                Exit;
              end
            else if Left^.Node.CodeType = cctIntConst then
              begin
                ResType := Right^.ResType;
                MakeTypeConversion( Left, ResType);
                Exit;
              end;
          end;
        Error( erCannotFindThisOperator, CodeTree^.Line, CodeTree^.Col, '');
      end;
  end;

procedure tOptomizer.DoOr( var CodeTree: pCodeTree);
  begin
    with Compiler^, CodeTree^ do
      begin
        if Left^.Node.CodeType = Right^.Node.CodeType then
          begin
            if Left^.Node.CodeType = cctBoolConst then
              begin
                Node.BoolValue := Left^.Node.BoolValue or Right^.Node.BoolValue;
                Node.CodeType := cctBoolConst;
                ResType := BoolDef;
{$IFDEF TP}
                Dispose( Left, Done);
                Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                Dispose( Left, Done());
                Dispose( Right, Done());
{$ENDIF}
                Left := nil;
                Right := nil;
                Exit;
              end
            else if Left^.Node.CodeType = cctIntConst then
              begin
                Node.IntValue := Left^.Node.IntValue or Right^.Node.IntValue;
                Node.CodeType := cctIntConst;
                ResType := LongDef;
{$IFDEF TP}
                Dispose( Left, Done);
                Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                Dispose( Left, Done());
                Dispose( Right, Done());
{$ENDIF}
                Left := nil;
                Right := nil;
                Exit;
              end;
          end;

        if FindOperator( cpoOr, CodeTree) then
          Exit;
        if (Left^.ResType^.DefType = cBooleanDefinition) and
          (Right^.ResType^.DefType = cBooleanDefinition) then
          begin
            ResType := Left^.ResType;
            Exit;
          end
        else if (Left^.ResType^.DefType = cOrdDefinition) and
          (Right^.ResType^.DefType = cOrdDefinition) and
          (pOrdDefinition(Left^.ResType)^.BaseType <> cbtChar) and
          (pOrdDefinition(Right^.ResType)^.BaseType <> cbtChar) then
          begin
{$IFDEF TP}
            if (Left^.ResType^.GetSize = Right^.ResType^.GetSize) then
{$ENDIF}
{$IFDEF PPRO}
            if (Left^.ResType^.GetSize() = Right^.ResType^.GetSize()) then
{$ENDIF}
              begin
                ResType := Left^.ResType;
                Exit;
              end
{$IFDEF TP}
            else if (Right^.Node.CodeType = cctIntConst) or
              ( ( Left^.Node.CodeType<> cctIntConst) and
              (Right^.ResType^.GetSize < Left^.ResType^.GetSize) ) then
{$ENDIF}
{$IFDEF PPRO}
            else if (Right^.Node.CodeType = cctIntConst) or
              ( ( Left^.Node.CodeType<> cctIntConst) and
              (Right^.ResType^.GetSize() < Left^.ResType^.GetSize()) ) then
{$ENDIF}
              begin
                ResType := Left^.ResType;
                MakeTypeConversion( Right, ResType);
                Exit;
              end
            else if Left^.Node.CodeType = cctIntConst then
              begin
                ResType := Right^.ResType;
                MakeTypeConversion( Left, ResType);
                Exit;
              end;
          end;
        Error( erCannotFindThisOperator, CodeTree^.Line, CodeTree^.Col, '');
      end;
  end;

procedure tOptomizer.DoXor( var CodeTree: pCodeTree);
  begin
    with Compiler^, CodeTree^ do
      begin
        if Left^.Node.CodeType = Right^.Node.CodeType then
          begin
            if Left^.Node.CodeType = cctBoolConst then
              begin
                Node.BoolValue := Left^.Node.BoolValue xor Right^.Node.BoolValue;
                Node.CodeType := cctBoolConst;
                ResType := BoolDef;
{$IFDEF TP}
                Dispose( Left, Done);
                Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                Dispose( Left, Done());
                Dispose( Right, Done());
{$ENDIF}
                Left := nil;
                Right := nil;
                Exit;
              end
            else if Left^.Node.CodeType = cctIntConst then
              begin
                Node.IntValue := Left^.Node.IntValue xor Right^.Node.IntValue;
                Node.CodeType := cctIntConst;
                ResType := LongDef;
{$IFDEF TP}
                Dispose( Left, Done);
                Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                Dispose( Left, Done());
                Dispose( Right, Done());
{$ENDIF}
                Left := nil;
                Right := nil;
                Exit;
              end;
          end;

        if FindOperator( cpoXor, CodeTree) then
          Exit;
        if (Left^.ResType^.DefType = cBooleanDefinition) and
          (Right^.ResType^.DefType = cBooleanDefinition) then
          begin
            ResType := Left^.ResType;
            Exit;
          end
        else if (Left^.ResType^.DefType = cOrdDefinition) and
          (Right^.ResType^.DefType = cOrdDefinition) and
          (pOrdDefinition(Left^.ResType)^.BaseType <> cbtChar) and
          (pOrdDefinition(Right^.ResType)^.BaseType <> cbtChar) then
          begin
{$IFDEF TP}
            if (Left^.ResType^.GetSize = Right^.ResType^.GetSize) then
{$ENDIF}
{$IFDEF PPRO}
            if (Left^.ResType^.GetSize() = Right^.ResType^.GetSize()) then
{$ENDIF}
              begin
                ResType := Left^.ResType;
                Exit;
              end
{$IFDEF TP}
            else if (Right^.Node.CodeType = cctIntConst) or
              ( ( Left^.Node.CodeType<> cctIntConst) and
              (Right^.ResType^.GetSize < Left^.ResType^.GetSize) ) then
{$ENDIF}
{$IFDEF PPRO}
            else if (Right^.Node.CodeType = cctIntConst) or
              ( ( Left^.Node.CodeType<> cctIntConst) and
              (Right^.ResType^.GetSize() < Left^.ResType^.GetSize()) ) then
{$ENDIF}
              begin
                ResType := Left^.ResType;
                MakeTypeConversion( Right, ResType);
                Exit;
              end
            else if Left^.Node.CodeType = cctIntConst then
              begin
                ResType := Right^.ResType;
                MakeTypeConversion( Left, ResType);
                Exit;
              end;
          end;
        Error( erCannotFindThisOperator, CodeTree^.Line, CodeTree^.Col, '');
      end;
  end;

procedure tOptomizer.DoShr( var CodeTree: pCodeTree);
  begin
    with Compiler^, CodeTree^ do
      begin
        if (Left^.Node.CodeType = cctIntConst) and
          (Right^.Node.CodeType = cctIntConst) then
          begin
            Node.IntValue := Left^.Node.IntValue shr Right^.Node.IntValue;
            Node.CodeType := cctIntConst;
            ResType := LongDef;
{$IFDEF TP}
            Dispose( Left, Done);
            Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
            Dispose( Left, Done());
            Dispose( Right, Done());
{$ENDIF}
            Left := nil;
            Right := nil;
            Exit;
          end;
        if FindOperator( cpoShr, CodeTree) then
          Exit;
        if (Left^.ResType^.DefType = cOrdDefinition) and
          (Right^.ResType^.DefType = cOrdDefinition) and
          (pOrdDefinition(Left^.ResType)^.BaseType <> cbtChar) and
          (pOrdDefinition(Right^.ResType)^.BaseType <> cbtChar) then
          begin
{$IFDEF TP}
            if (Left^.ResType^.GetSize = Right^.ResType^.GetSize) then
{$ENDIF}
{$IFDEF PPRO}
            if (Left^.ResType^.GetSize() = Right^.ResType^.GetSize()) then
{$ENDIF}
              begin
                ResType := Left^.ResType;
                Exit;
              end
{$IFDEF TP}
            else if (Right^.Node.CodeType = cctIntConst) or
              ( ( Left^.Node.CodeType<> cctIntConst) and
              (Right^.ResType^.GetSize < Left^.ResType^.GetSize) ) then
{$ENDIF}
{$IFDEF PPRO}
            else if (Right^.Node.CodeType = cctIntConst) or
              ( ( Left^.Node.CodeType<> cctIntConst) and
              (Right^.ResType^.GetSize() < Left^.ResType^.GetSize()) ) then
{$ENDIF}
              begin
                ResType := Left^.ResType;
                MakeTypeConversion( Right, ResType);
                Exit;
              end
            else if Left^.Node.CodeType = cctIntConst then
              begin
                ResType := Right^.ResType;
                MakeTypeConversion( Left, ResType);
                Exit;
              end;
          end;
        Error( erCannotFindThisOperator, CodeTree^.Line, CodeTree^.Col, '');
      end;
  end;

procedure tOptomizer.DoShl( var CodeTree: pCodeTree);
  begin
    with Compiler^, CodeTree^ do
      begin
        if (Left^.Node.CodeType = cctIntConst) and
          (Right^.Node.CodeType = cctIntConst) then
          begin
            Node.IntValue := Left^.Node.IntValue shl Right^.Node.IntValue;
            Node.CodeType := cctIntConst;
            ResType := LongDef;
{$IFDEF TP}
            Dispose( Left, Done);
            Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
            Dispose( Left, Done());
            Dispose( Right, Done());
{$ENDIF}
            Left := nil;
            Right := nil;
            Exit;
          end;

        if FindOperator( cpoShl, CodeTree) then
          Exit;
        if (Left^.ResType^.DefType = cOrdDefinition) and
          (Right^.ResType^.DefType = cOrdDefinition) and
          (pOrdDefinition(Left^.ResType)^.BaseType <> cbtChar) and
          (pOrdDefinition(Right^.ResType)^.BaseType <> cbtChar) then
          begin
{$IFDEF TP}
            if (Left^.ResType^.GetSize = Right^.ResType^.GetSize) then
{$ENDIF}
{$IFDEF PPRO}
            if (Left^.ResType^.GetSize() = Right^.ResType^.GetSize()) then
{$ENDIF}
              begin
                ResType := Left^.ResType;
                Exit;
              end
{$IFDEF TP}
            else if (Right^.Node.CodeType = cctIntConst) or
              ( ( Left^.Node.CodeType<> cctIntConst) and
              (Right^.ResType^.GetSize < Left^.ResType^.GetSize) ) then
{$ENDIF}
{$IFDEF PPRO}
            else if (Right^.Node.CodeType = cctIntConst) or
              ( ( Left^.Node.CodeType<> cctIntConst) and
              (Right^.ResType^.GetSize() < Left^.ResType^.GetSize()) ) then
{$ENDIF}
              begin
                ResType := Left^.ResType;
                MakeTypeConversion( Right, ResType);
                Exit;
              end
            else if Left^.Node.CodeType = cctIntConst then
              begin
                ResType := Right^.ResType;
                MakeTypeConversion( Left, ResType);
                Exit;
              end;
          end;
        Error( erCannotFindThisOperator, CodeTree^.Line, CodeTree^.Col, '');
      end;
  end;

procedure tOptomizer.DoEqual( var CodeTree: pCodeTree);
  var
    Tree: pCodeTree;
    S1, S2: pString;
  begin
    with Compiler^, CodeTree^ do
      begin
        if (Left^.Node.CodeType in [cctRealConst, cctIntConst, cctBoolConst, cctOrdConst]) and
          (Left^.Node.CodeType = Right^.Node.CodeType) then
          begin
              if Left^.ResType = Right^.ResType then
                begin
                  case Left^.Node.CodeType of
                    cctRealConst:
                      Node.BoolValue :=
                        Left^.Node.RealValue = Right^.Node.RealValue;
                    cctBoolConst:
                      Node.BoolValue :=
                        Left^.Node.BoolValue = Right^.Node.BoolValue;
                    cctCharConst:
                      Node.BoolValue :=
                        Left^.Node.CharValue = Right^.Node.CharValue;
                    cctIntConst:
                      Node.BoolValue :=
                        Left^.Node.IntValue = Right^.Node.IntValue;
                  end;
                  Node.CodeType := cctBoolConst;
                  ResType := BoolDef;
                  Dispose( Left, Done);
                  Dispose( Right, Done);
                  Left := nil;
                  Right := nil;
                  Exit;
                end;
          end
        else if (Left^.Node.CodeType = cctIntConst) and (Right^.Node.CodeType = cctRealConst) then
          begin
            Node.BoolValue := Left^.Node.IntValue = Right^.Node.RealValue;
            Node.CodeType := cctBoolConst;
            ResType := BoolDef;
            Dispose( Left, Done);
            Dispose( Right, Done);
            Left := nil;
            Right := nil;
            Exit;
          end
        else if (Left^.Node.CodeType = cctRealConst) and (Right^.Node.CodeType = cctIntConst) then
          begin
            Node.BoolValue := Left^.Node.RealValue = Right^.Node.IntValue;
            Node.CodeType := cctBoolConst;
            ResType := BoolDef;
            Dispose( Left, Done);
            Dispose( Right, Done);
            Left := nil;
            Right := nil;
            Exit;
          end
        else if (Left^.Node.CodeType in [ cctCharConst, cctStringConst]) and
          (Right^.Node.CodeType in [ cctCharConst, cctStringConst]) then
          begin
            if Left^.Node.CodeType = cctCharConst then
              S1 := NewStr( Left^.Node.CharValue)
            else
              S1 := NewStr( Left^.Node.StringValue^);
            if Right^.Node.CodeType = cctCharConst then
              S2 := NewStr( Right^.Node.CharValue)
            else
              S2 := NewStr( Right^.Node.StringValue^);
            Node.BoolValue := S1^ = S2^;
            Node.CodeType := cctBoolConst;
            ResType := BoolDef;
            Dispose( Left, Done);
            Dispose( Right, Done);
            Left := nil;
            Right := nil;
            DisposeStr( S1);
            DisposeStr( S2);
            Exit;
          end
        else if CodeTree^.Left^.Node.CodeType = cctSetConst then
          begin
            if (CodeTree^.Right^.Node.CodeType = cctSetConst) and
              CompatibleTypes( CodeTree^.Left^.ResType, CodeTree^.Right^.ResType) then
              begin
                Tree := New( pCodeTree, CreateBoolConst(
                  CodeTree^.Left^.Node.SetValue^ = CodeTree^.Right^.Node.SetValue^,
                  BoolDef,
                  CodeTree^.Left^.Line, CodeTree^.Left^.Col));
                Dispose( CodeTree, Done);
                CodeTree := Tree;
                Exit;
              end;
          end;

        if FindOperator( cpoEqual, CodeTree) then
          Exit;

        if (CodeTree^.Left^.ResType^.DefType = cSetDefinition) and
          (CodeTree^.Right^.ResType^.DefType = cSetDefinition) then
              begin
                if CompatibleTypes( CodeTree^.Left^.ResType,
                  CodeTree^.Right^.ResType) then
                  begin
                    CodeTree^.ResType := BoolDef;
                    Exit;
                  end;
              end
        else if ( CodeTree^.Left^.ResType^.DefType = cStringDefinition) then
          begin
            if CodeTree^.Right^.ResType^.DefType = cStringDefinition then
              begin
                CodeTree^.ResType := Compiler^.BoolDef;
                Exit;
              end
            else if (CodeTree^.Right^.ResType^.DefType = cOrdDefinition) and
              ( pOrdDefinition( CodeTree^.Right^.ResType)^.BaseType = cbtChar) then
              begin
                MakeTypeConversion( CodeTree^.Right, Compiler^.StringDef);
                CodeTree^.ResType := Compiler^.BoolDef;
                Exit;
              end;
          end
        else
        if (CodeTree^.Left^.ResType^.DefType = cOrdDefinition) and
          (CodeTree^.Right^.ResType^.DefType = cOrdDefinition) then
          if ( pOrdDefinition(CodeTree^.Left^.ResType)^.BaseType <> cbtChar) then
            begin
              if ( pOrdDefinition(CodeTree^.Right^.ResType)^.BaseType <> cbtChar) then
                begin
                  CodeTree^.ResType := Compiler^.BoolDef;
                  Exit;
                end;
            end
          else if ( pOrdDefinition(CodeTree^.Right^.ResType)^.BaseType = cbtChar) then
            begin
              CodeTree^.ResType := Compiler^.BoolDef;
              Exit;
            end
        else if (CodeTree^.Left^.ResType^.DefType = cOrdDefinition) and
          (pOrdDefinition( CodeTree^.Left^.ResType)^.BaseType = cbtChar) and
          (CodeTree^.Right^.ResType^.DefType = cStringDefinition) then
          begin
            MakeTypeConversion( CodeTree^.Left, Compiler^.StringDef);
            CodeTree^.ResType := Compiler^.BoolDef;
            Exit;
          end;

        if CodeTree^.Left^.ResType = CodeTree^.Right^.ResType then
          begin
            CodeTree^.ResType := Compiler^.BoolDef;
            Exit;
          end;
        if IsNumeric( CodeTree^.Left^.ResType) and
          IsNumeric( CodeTree^.Right^.ResType) then
          begin
            if CodeTree^.Left^.ResType^.DefType <> cRealDefinition then
              MakeTypeConversion( CodeTree^.Left, Compiler^.ExtendedDef)
            else if CodeTree^.Right^.ResType^.DefType <> cRealDefinition then
              MakeTypeConversion( CodeTree^.Right, Compiler^.ExtendedDef);
            CodeTree^.ResType := Compiler^.BoolDef;
            Exit;
          end;
       if EqualTypes(
         CodeTree^.Left^.ResType,
         CodeTree^.Right^.ResType) then
           begin
             CodeTree^.ResType := Compiler^.BoolDef;
             Exit;
           end;

        Error( erCannotFindThisOperator, CodeTree^.Line, CodeTree^.Col, '');
      end;
  end;

procedure tOptomizer.DoUnequal( var CodeTree: pCodeTree);
  var
    Tree: pCodeTree;
    S1, S2: pString;
  begin
    with Compiler^, CodeTree^ do
      begin
        if (Left^.Node.CodeType in [cctRealConst, cctIntConst, cctBoolConst, cctOrdConst]) and
          (Left^.Node.CodeType = Right^.Node.CodeType) then
          begin
              if Left^.ResType = Right^.ResType then
                begin
                  case Left^.Node.CodeType of
                    cctRealConst:
                      Node.BoolValue :=
                        Left^.Node.RealValue <> Right^.Node.RealValue;
                    cctBoolConst:
                      Node.BoolValue :=
                        Left^.Node.BoolValue <> Right^.Node.BoolValue;
                    cctCharConst:
                      Node.BoolValue :=
                        Left^.Node.CharValue <> Right^.Node.CharValue;
                    cctIntConst:
                      Node.BoolValue :=
                        Left^.Node.IntValue <> Right^.Node.IntValue;
                  end;
                  Node.CodeType := cctBoolConst;
                  ResType := BoolDef;
{$IFDEF TP}
                  Dispose( Left, Done);
                  Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                  Dispose( Left, Done());
                  Dispose( Right, Done());
{$ENDIF}
                  Left := nil;
                  Right := nil;
                  Exit;
                end;
          end
        else if (Left^.Node.CodeType = cctIntConst) and (Right^.Node.CodeType = cctRealConst) then
          begin
            Node.BoolValue := Left^.Node.IntValue <> Right^.Node.RealValue;
            Node.CodeType := cctBoolConst;
            ResType := BoolDef;
{$IFDEF TP}
            Dispose( Left, Done);
            Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
            Dispose( Left, Done());
            Dispose( Right, Done());
{$ENDIF}
            Left := nil;
            Right := nil;
            Exit;
          end
        else if (Left^.Node.CodeType = cctRealConst) and (Right^.Node.CodeType = cctIntConst) then
          begin
            Node.BoolValue := Left^.Node.RealValue <> Right^.Node.IntValue;
            Node.CodeType := cctBoolConst;
            ResType := BoolDef;
{$IFDEF TP}
            Dispose( Left, Done);
            Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
            Dispose( Left, Done());
            Dispose( Right, Done());
{$ENDIF}
            Left := nil;
            Right := nil;
            Exit;
          end
        else if (Left^.Node.CodeType in [ cctCharConst, cctStringConst]) and
          (Right^.Node.CodeType in [ cctCharConst, cctStringConst]) then
          begin
            if Left^.Node.CodeType = cctCharConst then
              S1 := NewStr( Left^.Node.CharValue)
            else
              S1 := NewStr( Left^.Node.StringValue^);
            if Right^.Node.CodeType = cctCharConst then
              S2 := NewStr( Right^.Node.CharValue)
            else
              S2 := NewStr( Right^.Node.StringValue^);
            Node.BoolValue := S1^ <> S2^;
            Node.CodeType := cctBoolConst;
            ResType := BoolDef;
{$IFDEF TP}
            Dispose( Left, Done);
            Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
            Dispose( Left, Done());
            Dispose( Right, Done());
{$ENDIF}
            Left := nil;
            Right := nil;
            DisposeStr( S1);
            DisposeStr( S2);
            Exit;
          end
      else if CodeTree^.Left^.Node.CodeType = cctSetConst then
        begin
          if (CodeTree^.Right^.Node.CodeType = cctSetConst) and
            CompatibleTypes( CodeTree^.Left^.ResType, CodeTree^.Right^.ResType) then
            begin
              Tree := New( pCodeTree, CreateBoolConst(
                CodeTree^.Left^.Node.SetValue^ <> CodeTree^.Right^.Node.SetValue^,
                BoolDef,
                CodeTree^.Left^.Line, CodeTree^.Left^.Col));
{$IFDEF TP}
              Dispose( CodeTree, Done);
{$ENDIF}
{$IFDEF PPRO}
              Dispose( CodeTree, Done());
{$ENDIF}
              CodeTree := Tree;
              Exit;
            end;
        end;

        if FindOperator( cpoUnequal, CodeTree) then
          Exit;

        if (CodeTree^.Left^.ResType^.DefType = cSetDefinition) and
          (CodeTree^.Right^.ResType^.DefType = cSetDefinition) then
              begin
                if CompatibleTypes( CodeTree^.Left^.ResType,
                  CodeTree^.Right^.ResType) then
                  begin
                    CodeTree^.ResType := BoolDef;
                    Exit;
                  end;
              end
        else if ( CodeTree^.Left^.ResType^.DefType = cStringDefinition) then
          begin
            if CodeTree^.Right^.ResType^.DefType = cStringDefinition then
              begin
                CodeTree^.ResType := Compiler^.BoolDef;
                Exit;
              end
            else if (CodeTree^.Right^.ResType^.DefType = cOrdDefinition) and
              ( pOrdDefinition( CodeTree^.Right^.ResType)^.BaseType = cbtChar) then
              begin
                MakeTypeConversion( CodeTree^.Right, Compiler^.StringDef);
                CodeTree^.ResType := Compiler^.BoolDef;
                Exit;
              end;
          end
        else
        if (CodeTree^.Left^.ResType^.DefType = cOrdDefinition) and
          (CodeTree^.Right^.ResType^.DefType = cOrdDefinition) then
          if ( pOrdDefinition(CodeTree^.Left^.ResType)^.BaseType <> cbtChar) then
            begin
              if ( pOrdDefinition(CodeTree^.Right^.ResType)^.BaseType <> cbtChar) then
                begin
                  CodeTree^.ResType := Compiler^.BoolDef;
                  Exit;
                end;
            end
          else if ( pOrdDefinition(CodeTree^.Right^.ResType)^.BaseType = cbtChar) then
            begin
              CodeTree^.ResType := Compiler^.BoolDef;
              Exit;
            end
        else if (CodeTree^.Left^.ResType^.DefType = cOrdDefinition) and
          (pOrdDefinition( CodeTree^.Left^.ResType)^.BaseType = cbtChar) and
          (CodeTree^.Right^.ResType^.DefType = cStringDefinition) then
          begin
            MakeTypeConversion( CodeTree^.Left, Compiler^.StringDef);
            CodeTree^.ResType := Compiler^.BoolDef;
            Exit;
          end;

        if CodeTree^.Left^.ResType = CodeTree^.Right^.ResType then
          begin
            CodeTree^.ResType := Compiler^.BoolDef;
            Exit;
          end;
        if IsNumeric( CodeTree^.Left^.ResType) and
          IsNumeric( CodeTree^.Right^.ResType) then
          begin
            if CodeTree^.Left^.ResType^.DefType <> cRealDefinition then
              MakeTypeConversion( CodeTree^.Left, Compiler^.ExtendedDef)
            else if CodeTree^.Right^.ResType^.DefType <> cRealDefinition then
              MakeTypeConversion( CodeTree^.Right, Compiler^.ExtendedDef);
            CodeTree^.ResType := Compiler^.BoolDef;
            Exit;
          end;
       if EqualTypes(
         CodeTree^.Left^.ResType,
         CodeTree^.Right^.ResType) then
           begin
             CodeTree^.ResType := Compiler^.BoolDef;
             Exit;
           end;

        Error( erCannotFindThisOperator, CodeTree^.Line, CodeTree^.Col, '');
      end;
  end;

procedure tOptomizer.DoGreater( var CodeTree: pCodeTree);
  var
    S1, S2: pString;
  begin
    with Compiler^, CodeTree^ do
      begin
        if (Left^.Node.CodeType in [cctRealConst, cctIntConst,
          cctBoolConst, cctOrdConst]) and
          (Left^.Node.CodeType = Right^.Node.CodeType) then
          begin
            if Left^.ResType = Right^.ResType then
                begin
                  case Left^.Node.CodeType of
                    cctRealConst:
                      Node.BoolValue :=
                        Left^.Node.RealValue > Right^.Node.RealValue;
                    cctBoolConst:
                      Node.BoolValue :=
                        Left^.Node.BoolValue > Right^.Node.BoolValue;
                    cctCharConst:
                      Node.BoolValue :=
                        Left^.Node.CharValue > Right^.Node.CharValue;
                    cctIntConst:
                      Node.BoolValue :=
                        Left^.Node.IntValue > Right^.Node.IntValue;
                  end;
                  Node.CodeType := cctBoolConst;
                  ResType := BoolDef;
{$IFDEF TP}
                  Dispose( Left, Done);
                  Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                  Dispose( Left, Done());
                  Dispose( Right, Done());
{$ENDIF}
                  Left := nil;
                  Right := nil;
                  Exit;
                end;
          end
        else if (Left^.Node.CodeType = cctIntConst) and (Right^.Node.CodeType = cctRealConst) then
          begin
            Node.BoolValue := Left^.Node.IntValue > Right^.Node.RealValue;
            Node.CodeType := cctBoolConst;
            ResType := BoolDef;
{$IFDEF TP}
            Dispose( Left, Done);
            Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
            Dispose( Left, Done());
            Dispose( Right, Done());
{$ENDIF}
            Left := nil;
            Right := nil;
            Exit;
          end
        else if (Left^.Node.CodeType = cctRealConst) and (Right^.Node.CodeType = cctIntConst) then
          begin
            Node.BoolValue := Left^.Node.RealValue > Right^.Node.IntValue;
            Node.CodeType := cctBoolConst;
            ResType := BoolDef;
{$IFDEF TP}
            Dispose( Left, Done);
            Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
            Dispose( Left, Done());
            Dispose( Right, Done());
{$ENDIF}
            Left := nil;
            Right := nil;
            Exit;
          end
        else if (Left^.Node.CodeType in [ cctCharConst, cctStringConst]) and
          (Right^.Node.CodeType in [ cctCharConst, cctStringConst]) then
          begin
            if Left^.Node.CodeType = cctCharConst then
              S1 := NewStr( Left^.Node.CharValue)
            else
              S1 := NewStr( Left^.Node.StringValue^);
            if Right^.Node.CodeType = cctCharConst then
              S2 := NewStr( Right^.Node.CharValue)
            else
              S2 := NewStr( Right^.Node.StringValue^);
            Node.BoolValue := S1^ > S2^;
            Node.CodeType := cctBoolConst;
            ResType := BoolDef;
{$IFDEF TP}
            Dispose( Left, Done);
            Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
            Dispose( Left, Done());
            Dispose( Right, Done());
{$ENDIF}
            Left := nil;
            Right := nil;
            DisposeStr( S1);
            DisposeStr( S2);
            Exit;
          end;

        if FindOperator( cpoGreater, CodeTree) then
          Exit;

        case CodeTree^.Left^.ResType^.DefType of
          cOrdDefinition:
            begin
              if pOrdDefinition(CodeTree^.Left^.ResType)^.BaseType = cbtChar
                then
                  begin
                    if (CodeTree^.Right^.ResType^.DefType = cOrdDefinition) and
                      (pOrdDefinition(CodeTree^.Right^.ResType)^.BaseType = cbtChar) then
                      begin
                        CodeTree^.ResType := Compiler^.BoolDef;
                        Exit;
                      end else
                    if ( CodeTree^.Right^.ResType^.DefType = cStringDefinition) then
                      begin
                        MakeTypeConversion( CodeTree^.Left, Compiler^.StringDef);
                        CodeTree^.ResType := Compiler^.BoolDef;
                        Exit;
                      end;
                  end
              else if IsNumeric( CodeTree^.Right^.ResType) then
                begin
                  if CodeTree^.Right^.ResType^.DefType = cRealDefinition then
                    MakeTypeConversion( CodeTree^.Left, Compiler^.ExtendedDef);
                  CodeTree^.ResType := Compiler^.BoolDef;
                  Exit;
                end;
            end;
          cRealDefinition: if IsNumeric( CodeTree^.Right^.ResType) then
            begin
              if CodeTree^.Right^.ResType^.DefType <> cRealDefinition then
                MakeTypeConversion( CodeTree^.Right, Compiler^.ExtendedDef);
              CodeTree^.ResType := Compiler^.BoolDef;
              Exit;
            end;
          cUserOrdDefinition:
            begin
              if CodeTree^.Left^.ResType = CodeTree^.Right^.ResType then
                begin
                  CodeTree^.ResType := Compiler^.BoolDef;
                  Exit;
                end;
            end;
          cStringDefinition:
            if CodeTree^.Right^.ResType^.DefType = cStringDefinition then
              begin
                CodeTree^.ResType := Compiler^.BoolDef;
                Exit;
              end
            else if (CodeTree^.Right^.ResType^.DefType = cOrdDefinition) and
              ( pOrdDefinition( CodeTree^.Right^.ResType)^.BaseType = cbtChar) then
              begin
                MakeTypeConversion( CodeTree^.Right, Compiler^.StringDef);
                CodeTree^.ResType := Compiler^.BoolDef;
                Exit;
              end;
          cBooleanDefinition:
            if CodeTree^.Right^.ResType^.DefType = cBooleanDefinition then
              begin
                CodeTree^.ResType := Compiler^.BoolDef;
                Exit;
              end;
        end;
        Error( erCannotFindThisOperator, CodeTree^.Line, CodeTree^.Col, '');
      end;
  end;

procedure tOptomizer.DoLess( var CodeTree: pCodeTree);
  var
    S1, S2: pString;
  begin
    with Compiler^, CodeTree^ do
      begin
        if (Left^.Node.CodeType in [cctRealConst, cctIntConst, cctBoolConst, cctOrdConst]) and
          (Left^.Node.CodeType = Right^.Node.CodeType) then
          begin
            if Left^.ResType = Right^.ResType then
                begin
                  case Left^.Node.CodeType of
                    cctRealConst:
                      Node.BoolValue :=
                        Left^.Node.RealValue < Right^.Node.RealValue;
                    cctBoolConst:
                      Node.BoolValue :=
                        Left^.Node.BoolValue < Right^.Node.BoolValue;
                    cctCharConst:
                      Node.BoolValue :=
                        Left^.Node.CharValue < Right^.Node.CharValue;
                    cctIntConst:
                      Node.BoolValue :=
                        Left^.Node.IntValue < Right^.Node.IntValue;
                  end;
                  Node.CodeType := cctBoolConst;
                  ResType := BoolDef;
{$IFDEF TP}
                  Dispose( Left, Done);
                  Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                  Dispose( Left, Done());
                  Dispose( Right, Done());
{$ENDIF}
                  Left := nil;
                  Right := nil;
                  Exit;
                end;
          end
        else if (Left^.Node.CodeType = cctIntConst) and (Right^.Node.CodeType = cctRealConst) then
          begin
            Node.BoolValue := Left^.Node.IntValue < Right^.Node.RealValue;
            Node.CodeType := cctBoolConst;
            ResType := BoolDef;
{$IFDEF TP}
            Dispose( Left, Done);
            Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
            Dispose( Left, Done());
            Dispose( Right, Done());
{$ENDIF}
            Left := nil;
            Right := nil;
            Exit;
          end
        else if (Left^.Node.CodeType = cctRealConst) and (Right^.Node.CodeType = cctIntConst) then
          begin
            Node.BoolValue := Left^.Node.RealValue < Right^.Node.IntValue;
            Node.CodeType := cctBoolConst;
            ResType := BoolDef;
{$IFDEF TP}
            Dispose( Left, Done);
            Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
            Dispose( Left, Done());
            Dispose( Right, Done());
{$ENDIF}
            Left := nil;
            Right := nil;
            Exit;
          end
        else if (Left^.Node.CodeType in [ cctCharConst, cctStringConst]) and
          (Right^.Node.CodeType in [ cctCharConst, cctStringConst]) then
          begin
            if Left^.Node.CodeType = cctCharConst then
              S1 := NewStr( Left^.Node.CharValue)
            else
              S1 := NewStr( Left^.Node.StringValue^);
            if Right^.Node.CodeType = cctCharConst then
              S2 := NewStr( Right^.Node.CharValue)
            else
              S2 := NewStr( Right^.Node.StringValue^);
            Node.BoolValue := S1^ < S2^;
            Node.CodeType := cctBoolConst;
            ResType := BoolDef;
{$IFDEF TP}
            Dispose( Left, Done);
            Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
            Dispose( Left, Done());
            Dispose( Right, Done());
{$ENDIF}
            Left := nil;
            Right := nil;
            DisposeStr( S1);
            DisposeStr( S2);
            Exit;
          end;

        if FindOperator( cpoLess, CodeTree) then
          Exit;

        case CodeTree^.Left^.ResType^.DefType of
          cOrdDefinition:
            begin
              if pOrdDefinition(CodeTree^.Left^.ResType)^.BaseType = cbtChar
                then
                  begin
                    if (CodeTree^.Right^.ResType^.DefType = cOrdDefinition) and
                      (pOrdDefinition(CodeTree^.Right^.ResType)^.BaseType = cbtChar) then
                      begin
                        CodeTree^.ResType := Compiler^.BoolDef;
                        Exit;
                      end else
                    if ( CodeTree^.Right^.ResType^.DefType = cStringDefinition) then
                      begin
                        MakeTypeConversion( CodeTree^.Left, Compiler^.StringDef);
                        CodeTree^.ResType := Compiler^.BoolDef;
                        Exit;
                      end;
                  end
              else if IsNumeric( CodeTree^.Right^.ResType) then
                begin
                  if CodeTree^.Right^.ResType^.DefType = cRealDefinition then
                    MakeTypeConversion( CodeTree^.Left, Compiler^.ExtendedDef);
                  CodeTree^.ResType := Compiler^.BoolDef;
                  Exit;
                end;
            end;
          cRealDefinition: if IsNumeric( CodeTree^.Right^.ResType) then
            begin
              if CodeTree^.Right^.ResType^.DefType <> cRealDefinition then
                MakeTypeConversion( CodeTree^.Right, Compiler^.ExtendedDef);
              CodeTree^.ResType := Compiler^.BoolDef;
              Exit;
            end;
          cUserOrdDefinition:
            begin
              if CodeTree^.Left^.ResType = CodeTree^.Right^.ResType then
                begin
                  CodeTree^.ResType := Compiler^.BoolDef;
                  Exit;
                end;
            end;
          cStringDefinition:
            if CodeTree^.Right^.ResType^.DefType = cStringDefinition then
              begin
                CodeTree^.ResType := Compiler^.BoolDef;
                Exit;
              end
            else if (CodeTree^.Right^.ResType^.DefType = cOrdDefinition) and
              ( pOrdDefinition( CodeTree^.Right^.ResType)^.BaseType = cbtChar) then
              begin
                MakeTypeConversion( CodeTree^.Right, Compiler^.StringDef);
                CodeTree^.ResType := Compiler^.BoolDef;
                Exit;
              end;
          cBooleanDefinition:
            if CodeTree^.Right^.ResType^.DefType = cBooleanDefinition then
              begin
                CodeTree^.ResType := Compiler^.BoolDef;
                Exit;
              end;
        end;
        Error( erCannotFindThisOperator, CodeTree^.Line, CodeTree^.Col, '');
      end;
  end;

procedure tOptomizer.DoGreaterEqual( var CodeTree: pCodeTree);
  var
    Tree: pCodeTree;
    S1, S2: pString;
  begin
    with Compiler^, CodeTree^ do
      begin
        if (Left^.Node.CodeType in [cctRealConst, cctIntConst, cctBoolConst, cctOrdConst]) and
          (Left^.Node.CodeType = Right^.Node.CodeType) then
          begin
            if Left^.ResType = Right^.ResType then
                begin
                  case Left^.Node.CodeType of
                    cctRealConst:
                      Node.BoolValue :=
                        Left^.Node.RealValue >= Right^.Node.RealValue;
                    cctBoolConst:
                      Node.BoolValue :=
                        Left^.Node.BoolValue >= Right^.Node.BoolValue;
                    cctCharConst:
                      Node.BoolValue :=
                        Left^.Node.CharValue >= Right^.Node.CharValue;
                    cctIntConst:
                      Node.BoolValue :=
                        Left^.Node.IntValue >= Right^.Node.IntValue;
                  end;
                  Node.CodeType := cctBoolConst;
                  ResType := BoolDef;
{$IFDEF TP}
                  Dispose( Left, Done);
                  Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                  Dispose( Left, Done());
                  Dispose( Right, Done());
{$ENDIF}
                  Left := nil;
                  Right := nil;
                  Exit;
                end;
          end
        else if (Left^.Node.CodeType = cctIntConst) and (Right^.Node.CodeType = cctRealConst) then
          begin
            Node.BoolValue := Left^.Node.IntValue >= Right^.Node.RealValue;
            Node.CodeType := cctBoolConst;
            ResType := BoolDef;
{$IFDEF TP}
            Dispose( Left, Done);
            Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
            Dispose( Left, Done());
            Dispose( Right, Done());
{$ENDIF}
            Left := nil;
            Right := nil;
            Exit;
          end
        else if (Left^.Node.CodeType = cctRealConst) and (Right^.Node.CodeType = cctIntConst) then
          begin
            Node.BoolValue := Left^.Node.RealValue >= Right^.Node.IntValue;
            Node.CodeType := cctBoolConst;
            ResType := BoolDef;
{$IFDEF TP}
            Dispose( Left, Done);
            Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
            Dispose( Left, Done());
            Dispose( Right, Done());
{$ENDIF}
            Left := nil;
            Right := nil;
            Exit;
          end
        else if (Left^.Node.CodeType in [ cctCharConst, cctStringConst]) and
          (Right^.Node.CodeType in [ cctCharConst, cctStringConst]) then
          begin
            if Left^.Node.CodeType = cctCharConst then
              S1 := NewStr( Left^.Node.CharValue)
            else
              S1 := NewStr( Left^.Node.StringValue^);
            if Right^.Node.CodeType = cctCharConst then
              S2 := NewStr( Right^.Node.CharValue)
            else
              S2 := NewStr( Right^.Node.StringValue^);
            Node.BoolValue := S1^ >= S2^;
            Node.CodeType := cctBoolConst;
            ResType := BoolDef;
{$IFDEF TP}
            Dispose( Left, Done);
            Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
            Dispose( Left, Done());
            Dispose( Right, Done());
{$ENDIF}
            Left := nil;
            Right := nil;
            DisposeStr( S1);
            DisposeStr( S2);
            Exit;
          end
        else if CodeTree^.Left^.Node.CodeType = cctSetConst then
          begin
            if (CodeTree^.Right^.Node.CodeType = cctSetConst) and
              CompatibleTypes( CodeTree^.Left^.ResType, CodeTree^.Right^.ResType) then
              begin
                Tree := New( pCodeTree, CreateBoolConst(
                  CodeTree^.Left^.Node.SetValue^ >= CodeTree^.Right^.Node.SetValue^,
                  BoolDef,
                  CodeTree^.Left^.Line, CodeTree^.Left^.Col));
{$IFDEF TP}
                Dispose( CodeTree, Done);
{$ENDIF}
{$IFDEF PPRO}
                Dispose( CodeTree, Done());
{$ENDIF}
                CodeTree := Tree;
                Exit;
              end;
          end;

        if FindOperator( cpoGreaterEqual, CodeTree) then
          Exit;

        case CodeTree^.Left^.ResType^.DefType of
          cOrdDefinition:
            begin
              if pOrdDefinition(CodeTree^.Left^.ResType)^.BaseType = cbtChar
                then
                  begin
                    if (CodeTree^.Right^.ResType^.DefType = cOrdDefinition) and
                      (pOrdDefinition(CodeTree^.Right^.ResType)^.BaseType = cbtChar) then
                      begin
                        CodeTree^.ResType := Compiler^.BoolDef;
                        Exit;
                      end else
                    if ( CodeTree^.Right^.ResType^.DefType = cStringDefinition) then
                      begin
                        MakeTypeConversion( CodeTree^.Left, Compiler^.StringDef);
                        CodeTree^.ResType := Compiler^.BoolDef;
                        Exit;
                      end;
                  end
              else if IsNumeric( CodeTree^.Right^.ResType) then
                begin
                  if CodeTree^.Right^.ResType^.DefType = cRealDefinition then
                    MakeTypeConversion( CodeTree^.Left, Compiler^.ExtendedDef);
                  CodeTree^.ResType := Compiler^.BoolDef;
                  Exit;
                end;
            end;
          cRealDefinition: if IsNumeric( CodeTree^.Right^.ResType) then
            begin
              if CodeTree^.Right^.ResType^.DefType <> cRealDefinition then
                MakeTypeConversion( CodeTree^.Right, Compiler^.ExtendedDef);
              CodeTree^.ResType := Compiler^.BoolDef;
              Exit;
            end;
          cUserOrdDefinition:
            begin
              if CodeTree^.Left^.ResType = CodeTree^.Right^.ResType then
                begin
                  CodeTree^.ResType := Compiler^.BoolDef;
                  Exit;
                end;
            end;
          cStringDefinition:
            if CodeTree^.Right^.ResType^.DefType = cStringDefinition then
              begin
                CodeTree^.ResType := Compiler^.BoolDef;
                Exit;
              end
            else if (CodeTree^.Right^.ResType^.DefType = cOrdDefinition) and
              ( pOrdDefinition( CodeTree^.Right^.ResType)^.BaseType = cbtChar) then
              begin
                MakeTypeConversion( CodeTree^.Right, Compiler^.StringDef);
                CodeTree^.ResType := Compiler^.BoolDef;
                Exit;
              end;
          cSetDefinition:
            if (CodeTree^.Right^.ResType^.DefType = cSetDefinition) then
              begin
                if CompatibleTypes( CodeTree^.Left^.ResType,
                  CodeTree^.Right^.ResType) then
                  begin
                    CodeTree^.ResType := BoolDef;
                    Exit;
                  end;
              end;
          cBooleanDefinition:
            if CodeTree^.Right^.ResType^.DefType = cBooleanDefinition then
              begin
                CodeTree^.ResType := Compiler^.BoolDef;
                Exit;
              end;
        end;
        Error( erCannotFindThisOperator, CodeTree^.Line, CodeTree^.Col, '');
      end;
  end;

procedure tOptomizer.DoLessEqual( var CodeTree: pCodeTree);
  var
    Tree: pCodeTree;
    S1, S2: pString;
  begin
    with Compiler^, CodeTree^ do
      begin
        if (Left^.Node.CodeType in [cctRealConst, cctIntConst, cctBoolConst, cctOrdConst]) and
          (Left^.Node.CodeType = Right^.Node.CodeType) then
          begin
            if Left^.ResType = Right^.ResType then
                begin
                  case Left^.Node.CodeType of
                    cctRealConst:
                      Node.BoolValue :=
                        Left^.Node.RealValue <= Right^.Node.RealValue;
                    cctBoolConst:
                      Node.BoolValue :=
                        Left^.Node.BoolValue <= Right^.Node.BoolValue;
                    cctCharConst:
                      Node.BoolValue :=
                        Left^.Node.CharValue <= Right^.Node.CharValue;
                    cctIntConst:
                      Node.BoolValue :=
                        Left^.Node.IntValue <= Right^.Node.IntValue;
                  end;
                  Node.CodeType := cctBoolConst;
                  ResType := BoolDef;
{$IFDEF TP}
                  Dispose( Left, Done);
                  Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                  Dispose( Left, Done());
                  Dispose( Right, Done());
{$ENDIF}
                  Left := nil;
                  Right := nil;
                  Exit;
                end;
          end
        else if (Left^.Node.CodeType = cctIntConst) and (Right^.Node.CodeType = cctRealConst) then
          begin
            Node.BoolValue := Left^.Node.IntValue <= Right^.Node.RealValue;
            Node.CodeType := cctBoolConst;
            ResType := BoolDef;
{$IFDEF TP}
                  Dispose( Left, Done);
                  Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
                  Dispose( Left, Done());
                  Dispose( Right, Done());
{$ENDIF}
            Left := nil;
            Right := nil;
            Exit;
          end
        else if (Left^.Node.CodeType = cctRealConst) and (Right^.Node.CodeType = cctIntConst) then
          begin
            Node.BoolValue := Left^.Node.RealValue <= Right^.Node.IntValue;
            Node.CodeType := cctBoolConst;
            ResType := BoolDef;
{$IFDEF TP}
            Dispose( Left, Done);
            Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
            Dispose( Left, Done());
            Dispose( Right, Done());
{$ENDIF}
            Left := nil;
            Right := nil;
            Exit;
          end
        else if (Left^.Node.CodeType in [ cctCharConst, cctStringConst]) and
          (Right^.Node.CodeType in [ cctCharConst, cctStringConst]) then
          begin
            if Left^.Node.CodeType = cctCharConst then
              S1 := NewStr( Left^.Node.CharValue)
            else
              S1 := NewStr( Left^.Node.StringValue^);
            if Right^.Node.CodeType = cctCharConst then
              S2 := NewStr( Right^.Node.CharValue)
            else
              S2 := NewStr( Right^.Node.StringValue^);
            Node.BoolValue := S1^ <= S2^;
            Node.CodeType := cctBoolConst;
            ResType := BoolDef;
{$IFDEF TP}
            Dispose( Left, Done);
            Dispose( Right, Done);
{$ENDIF}
{$IFDEF PPRO}
            Dispose( Left, Done());
            Dispose( Right, Done());
{$ENDIF}
            Left := nil;
            Right := nil;
            DisposeStr( S1);
            DisposeStr( S2);
            Exit;
          end
        else if CodeTree^.Left^.Node.CodeType = cctSetConst then
          begin
            if (CodeTree^.Right^.Node.CodeType = cctSetConst) and
              CompatibleTypes( CodeTree^.Left^.ResType, CodeTree^.Right^.ResType) then
              begin
                Tree := New( pCodeTree, CreateBoolConst(
                  CodeTree^.Left^.Node.SetValue^ <= CodeTree^.Right^.Node.SetValue^,
                  BoolDef,
                  CodeTree^.Left^.Line, CodeTree^.Left^.Col));
{$IFDEF TP}
                Dispose( CodeTree, Done);
{$ENDIF}
{$IFDEF PPRO}
                Dispose( CodeTree, Done());
{$ENDIF}
                CodeTree := Tree;
                Exit;
              end;
          end;

        if FindOperator( cpoLessEqual, CodeTree) then
          Exit;

        case CodeTree^.Left^.ResType^.DefType of
          cOrdDefinition:
            begin
              if pOrdDefinition(CodeTree^.Left^.ResType)^.BaseType = cbtChar
                then
                  begin
                    if (CodeTree^.Right^.ResType^.DefType = cOrdDefinition) and
                      (pOrdDefinition(CodeTree^.Right^.ResType)^.BaseType = cbtChar) then
                      begin
                        CodeTree^.ResType := Compiler^.BoolDef;
                        Exit;
                      end else
                    if ( CodeTree^.Right^.ResType^.DefType = cStringDefinition) then
                      begin
                        MakeTypeConversion( CodeTree^.Left, Compiler^.StringDef);
                        CodeTree^.ResType := Compiler^.BoolDef;
                        Exit;
                      end;
                  end
              else if IsNumeric( CodeTree^.Right^.ResType) then
                begin
                  if CodeTree^.Right^.ResType^.DefType = cRealDefinition then
                    MakeTypeConversion( CodeTree^.Left, Compiler^.ExtendedDef);
                  CodeTree^.ResType := Compiler^.BoolDef;
                  Exit;
                end;
            end;
          cRealDefinition: if IsNumeric( CodeTree^.Right^.ResType) then
            begin
              if CodeTree^.Right^.ResType^.DefType <> cRealDefinition then
                MakeTypeConversion( CodeTree^.Right, Compiler^.ExtendedDef);
              CodeTree^.ResType := Compiler^.BoolDef;
              Exit;
            end;
          cUserOrdDefinition:
            begin
              if CodeTree^.Left^.ResType = CodeTree^.Right^.ResType then
                begin
                  CodeTree^.ResType := Compiler^.BoolDef;
                  Exit;
                end;
            end;
          cStringDefinition:
            if CodeTree^.Right^.ResType^.DefType = cStringDefinition then
              begin
                CodeTree^.ResType := Compiler^.BoolDef;
                Exit;
              end
            else if (CodeTree^.Right^.ResType^.DefType = cOrdDefinition) and
              ( pOrdDefinition( CodeTree^.Right^.ResType)^.BaseType = cbtChar) then
              begin
                MakeTypeConversion( CodeTree^.Right, Compiler^.StringDef);
                CodeTree^.ResType := Compiler^.BoolDef;
                Exit;
              end;
          cSetDefinition:
            if (CodeTree^.Right^.ResType^.DefType = cSetDefinition) then
              begin
                if CompatibleTypes( CodeTree^.Left^.ResType,
                  CodeTree^.Right^.ResType) then
                  begin
                    CodeTree^.ResType := BoolDef;
                    Exit;
                  end;
              end;
          cBooleanDefinition:
            if CodeTree^.Right^.ResType^.DefType = cBooleanDefinition then
              begin
                CodeTree^.ResType := Compiler^.BoolDef;
                Exit;
              end;
        end;
        Error( erCannotFindThisOperator, CodeTree^.Line, CodeTree^.Col, '');
      end;
  end;

procedure tOptomizer.DoIN( var CodeTree: pCodeTree);
  begin
    with Compiler^, CodeTree^ do
      begin
        if (Left^.Node.CodeType in [cctIntConst, cctOrdConst]) and
          (Right^.Node.CodeType = cctSetConst) then
          begin
            if CompatibleTypes( Left^.ResType,
              pSetDefinition( Right^.ResType)^.SetDef ) then
                begin
                  Node.BoolValue :=
                    Left^.Node.IntValue in Right^.Node.SetValue^;
                  Node.CodeType := cctBoolConst;
                  ResType := BoolDef;
                  Dispose( Left, Done);
                  Dispose( Right, Done);
                  Left := nil;
                  Right := nil;
                  Exit;
                end;
          end;

        if FindOperator( cpoIN, CodeTree) then
          Exit;

        if CodeTree^.Left^.ResType^.DefType in
          [cOrdDefinition, cUserOrdDefinition] then
          begin
            if CompatibleTypes( Left^.ResType,
              pSetDefinition( Right^.ResType)^.SetDef ) then
                begin
                  ResType := BoolDef;
                  Exit;
                end;
          end;
        Error( erCannotFindThisOperator, CodeTree^.Line, CodeTree^.Col, '');
      end;
  end;

procedure tOptomizer.DoAssignment( var CodeTree: pCodeTree);
  begin
    with CodeTree^ do
      begin
        if FindOperator( cpoAssignment, CodeTree) then
          Exit;
        if Left^.ResType <> Right^.ResType then
          begin
            case CodeTree^.Left^.ResType^.DefType of
              cOrdDefinition:
                begin
                  case pOrdDefinition(Left^.ResType)^.BaseType of
                    cbtByte, cbtShortInt, cbtInteger,
                    cbtWord, cbtLongInt, cbtDWord:
                      if Right^.Node.CodeType = cctIntConst then
                        begin
                          ResType := Left^.ResType;
                          Right^.ResType := ResType;
                          Exit;
                        end
                      else if (Right^.ResType^.DefType = cOrdDefinition)
                        and (pOrdDefinition(Right^.ResType)^.BaseType <> cbtChar) then
                        begin
                          ResType := Left^.ResType;
                          MakeTypeConversion( Right, ResType);
                          Exit;
                        end;
                    else
                      if (Right^.ResType^.DefType = cOrdDefinition) and
                        (pOrdDefinition(Right^.ResType)^.BaseType = cbtChar) then
                        begin
                          ResType := Left^.ResType;
                          Exit;
                        end;
                  end;
                end;
            end;
            if not CompatibleTypes( Left^.ResType, Right^.ResType) then
              Compiler^.Error( erCannotFindThisOperator, Line, Col, '')
            else if (Left^.ResType^.DefType = cFileDefinition) or
              (Right^.ResType^.DefType = cFileDefinition) then
              Compiler^.Error( erCannotFindThisOperator, Line, Col, '')
            else
              begin
                if Left^.ResType^.DefType <> cSetDefinition then
                  MakeTypeConversion( Right, Left^.ResType);
                ResType := Left^.ResType;
              end;
          end
        else if (Left^.ResType^.DefType = cFileDefinition) or
          (Right^.ResType^.DefType = cFileDefinition) then
          Compiler^.Error( erCannotFindThisOperator, Line, Col, '')
        else
          ResType := Left^.ResType;
      end;
  end;

procedure tOptomizer.DoAsn( var CodeTree: pCodeTree);
  var
    PasOp: tPasOperators;
  begin
    case CodeTree^.Node.CodeType of
      cctPlusAsn:
        PasOp := cpoPlusAsn;
      cctMinusAsn:
        PasOp := cpoMinusAsn;
      cctAndAsn:
        PasOp := cpoAndAsn;
      cctOrAsn:
        PasOp := cpoOrAsn;
      cctStarAsn:
        PasOp := cpoStarAsn;
      cctSlashAsn:
        PasOp := cpoSlashAsn;
      cctDivAsn:
        PasOp := cpoDivAsn;
      cctModAsn:
        PasOp := cpoModAsn;
      cctShlAsn:
        PasOp := cpoShlAsn;
      cctShrAsn:
        PasOp := cpoShrAsn;
      cctXorAsn:
        PasOp := cpoXorAsn;
      else
        Compiler^.Error( erInternalError, Compiler^.Files^.PrevLine, Compiler^.Files^.PrevCol, '');
    end;
    if FindOperator( PasOp, CodeTree) then
      Exit;
    Compiler^.Error( erCannotFindThisOperator, CodeTree^.Line, CodeTree^.Col, '');
 end;

procedure tOptomizer.DoVariable( var CodeTree: pCodeTree);
  begin
  end;

procedure tOptomizer.DoLoadValue( var CodeTree: pCodeTree);
  begin
  end;


procedure tOptomizer.DoAsmBlock( var CodeTree: pCodeTree);
  begin
  end;

procedure tOptomizer.DoPred( var CodeTree: pCodeTree);
  var
    Expr: pCodeTree;
  begin
    if CodeTree^.Left^.Node.CodeType in [cctIntConst, cctBoolConst,
      cctOrdConst, cctCharConst] then
      begin
        Dec( CodeTree^.Left^.Node.IntValue);
        Expr := CodeTree^.Left;
        CodeTree^.Left := nil;
        Dispose( CodeTree, Done);
        CodeTree := Expr;
      end;
  end;

procedure tOptomizer.DoSucc( var CodeTree: pCodeTree);
  var
    Expr: pCodeTree;
  begin
    if CodeTree^.Left^.Node.CodeType in [cctIntConst, cctBoolConst,
      cctOrdConst, cctCharConst] then
      begin
        Inc( CodeTree^.Left^.Node.IntValue);
        Expr := CodeTree^.Left;
        CodeTree^.Left := nil;
        Dispose( CodeTree, Done);
        CodeTree := Expr;
      end;
  end;


procedure tOptomizer.DoSetItem( var CodeTree: pCodeTree);
  var
    Tree: pCodeTree;
  begin
    if Assigned( CodeTree^.Left) and
      (CodeTree^.Left^.Node.CodeType in [cctIntConst, cctCharConst, cctOrdConst]) then
      begin
        if (CodeTree^.Left^.Node.IntValue > 255) or
          (CodeTree^.Left^.Node.IntValue < 0) then
          Compiler^.Error( erConstantOutOfRange,
            Compiler^.Files^.PrevLine, Compiler^.Files^.PrevCol, ToStr( CodeTree^.Left^.Node.IntValue));
{writeln( '-', codetree^.left^.node.intvalue, '-');}
        Tree := New( pCodeTree, CreateSetConst(
          [CodeTree^.Left^.Node.IntValue], CodeTree^.ResType, 0, 0));
        Tree^.DisposeType := CodeTree^.DisposeType;
        CodeTree^.DisposeType := CodeTree^.DisposeType and not cdtDisposeResult;
        Dispose( CodeTree, Done);
        CodeTree := Tree;
      end;
  end;

procedure tOptomizer.DoSetRange( var CodeTree: pCodeTree);
  var
    Tree: pCodeTree;
  begin
    if Assigned( CodeTree^.Left) and
      (CodeTree^.Left^.Node.CodeType in [cctIntConst, cctCharConst, cctOrdConst]) and
      Assigned( CodeTree^.Right) and
      (CodeTree^.Right^.Node.CodeType in [cctIntConst, cctCharConst, cctOrdConst]) then
      begin
        if (CodeTree^.Left^.Node.IntValue > 255) or
          (CodeTree^.Left^.Node.IntValue < 0) then
          Compiler^.Error( erConstantOutOfRange,
            CodeTree^.Left^.Line, CodeTree^.Left^.Col, ToStr( CodeTree^.Left^.Node.IntValue));
        if (CodeTree^.Right^.Node.IntValue > 255) or
          (CodeTree^.Right^.Node.IntValue < 0) then
          Compiler^.Error( erConstantOutOfRange,
            CodeTree^.Right^.Line, CodeTree^.Right^.Col, ToStr( CodeTree^.Right^.Node.IntValue));
        if (CodeTree^.Right^.Node.IntValue < CodeTree^.Left^.Node.IntValue) then
          Compiler^.Error( erLowerBoundGreaterThanUpperBound,
            CodeTree^.Left^.Line, CodeTree^.Left^.Col, '');
        Tree := New( pCodeTree, CreateSetConst(
          [CodeTree^.Left^.Node.IntValue..CodeTree^.Right^.Node.IntValue],
          CodeTree^.ResType, 0, 0));
        Tree^.DisposeType := CodeTree^.DisposeType;
        CodeTree^.DisposeType := CodeTree^.DisposeType and not cdtDisposeResult;
        Dispose( CodeTree, Done);
        CodeTree := Tree;
      end;
  end;


procedure tOptomizer.DoArithmeticFunction( var CodeTree: pCodeTree);
  var
    Res: Extended;
    iRes: LongInt;
  begin
    case CodeTree^.Left^.Node.CodeType of
      cctRealConst:
        begin
          Res := CodeTree^.Left^.Node.RealValue;
          case CodeTree^.Node.SysSymbolType of
            csstSin:
              Res := sin( Res );
            csstCos:
              Res := cos( Res );
            csstTan:
              Res := sin( Res ) / cos( Res );
            csstCotan:
              Res := cos( Res) / sin( Res );
            csstArcTan:
              Res := arctan( Res );
            csstSqr:
              Res := sqr( res );
            csstSqrt:
              Res := sqrt( res );
            csstAbs:
              Res := Abs( res );
          end;
          Dispose( CodeTree^.Left, Done);
          CodeTree^.Node.CodeType := cctRealConst;
          CodeTree^.Node.RealValue := Res;
          CodeTree^.Left := nil;
        end;
      cctIntConst:
        begin
          iRes := CodeTree^.Left^.Node.IntValue;
          case CodeTree^.Node.SysSymbolType of
            csstODD:
              begin
                CodeTree^.Node.CodeType := cctBoolConst;
                CodeTree^.Node.BoolValue := Odd( iRes);
              end;
            csstABS:
              begin
                CodeTree^.Node.CodeType := cctIntConst;
                CodeTree^.Node.IntValue := Abs( iRes);
              end;
          end;
          Dispose( CodeTree^.Left, Done);
          CodeTree^.Left := nil;
        end;
    end;
  end;


function tOptomizer.FindOperator( PasOp: tPasOperators; var CodeTree: pCodeTree): Boolean;
  var
    ParamColl, P: pDefCollection;
    Sym: pFunctionSymbol;
    Expr: pCodeTree;
    Lev: LongInt;
  begin
    ParamColl := nil;
    FindOperator := False;
    if Assigned( CodeTree) and (PasOp <> cpoUnknown) then
      begin
        if Assigned( CodeTree^.Left) then
          begin
            New( ParamColl);
            ParamColl^.Definition := CodeTree^.Left^.ResType;
            ParamColl^.ParamType := GetParamType( CodeTree^.Left);
            ParamColl^.Next := nil;
            if Assigned( CodeTree^.Right) then
              begin
                New( P);
                with P^ do
                  begin
                    Definition := CodeTree^.Right^.ResType;
                    ParamType := GetParamType( CodeTree^.Right);
                    Next := ParamColl;
                  end;
                ParamColl := P;
              end;
          end;
        Sym := Compiler^.FindFunction( OperatorNames[ PasOp], ParamColl, nil, Lev, nil);
        DisposeDefCollection( ParamColl);
        if Assigned( Sym) then
          begin
            ParamColl := Sym^.Definition^.ParamColl;
            Expr := nil;
            if Assigned( CodeTree^.Left) then
              begin
                Expr := New( pCodeTree, CreateFuncParam( Expr, CodeTree^.Left));
                Expr^.ResType := ParamColl^.Definition;
                MakeTypeConversion( Expr^.Right, ParamColl^.Definition);
                if ParamColl^.ParamType in [ cvtVarParam, cvtConstParam] then
                  Expr^.Right := New( pCodeTree,
                    CreateLoadAddress( Expr^.Right, Compiler^.PointerDef));
                ParamColl := ParamColl^.Next;
                if Assigned( CodeTree^.Right) then
                  begin
                    Expr := New( pCodeTree, CreateFuncParam( Expr, CodeTree^.Right));
                    Expr^.ResType := ParamColl^.Definition;
                    MakeTypeConversion( Expr^.Right, ParamColl^.Definition);
                    if ParamColl^.ParamType in [ cvtVarParam, cvtConstParam] then
                      Expr^.Right := New( pCodeTree,
                        CreateLoadAddress( Expr^.Right, Compiler^.PointerDef));
                  end;
              end;
            CodeTree^.Left := nil;
            CodeTree^.Right := nil;
            Dispose( CodeTree, Done);
            CodeTree := New( pCodeTree, CreateFunctionCall(
              New( pCodeTree, CreateFunction( Sym, nil)),
              Expr, nil, 0, 0));
            FindOperator := True;
            Exit;
          end;
      end;
  end;

procedure tOptomizer.DoLength( var CodeTree: pCodeTree);
  begin
    if CodeTree^.Left^.Node.CodeType = cctStringConst then
      begin
        CodeTree^.Node.CodeType := cctIntConst;
        CodeTree^.Node.IntValue := Length( CodeTree^.Left^.Node.StringValue^);
        Dispose( CodeTree^.Left, Done);
        CodeTree^.Left := nil;
      end;
  end;


procedure tOptomizer.DoFunctionCall( var CodeTree: pCodeTree);
  begin
    if not Assigned( CodeTree^.ResType) then
      case CodeTree^.Left^.Node.CodeType of
        cctFunction:
          CodeTree^.ResType := CodeTree^.Left^.Node.FuncSym^.Definition^.ResType;
        else
          if CodeTree^.Left^.ResType^.DefType = cFunctionTypeDefinition then
            CodeTree^.ResType := pFunctionTypeDefinition( CodeTree^.Left^.ResType)^.ResType;
      end;
  end;


procedure tOptomizer.DoIfExpression( var CodeTree: pCodeTree);
  begin
    DoExpression( CodeTree^.Right);
    DoExpression( CodeTree^.Node.IfBlock);
    DoExpression( CodeTree^.Node.ElseBlock);
    CodeTree^.ResType := CodeTree^.Node.IfBlock^.ResType;
  end;


end.