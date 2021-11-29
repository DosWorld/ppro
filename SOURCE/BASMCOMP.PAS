{-----------------------------------------------------------------------}
{    Pascal Pro                                                         }
{       BasmComp unit                                                   }
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

unit BAsmComp;

interface

uses Objects, IAsm386, AsmOpt, AsmCode, Scanner, Symbols, Code;

type

  tAsmToken = (
    catNone,
    catOpCode,
    catPrefix,
    catRegister,
    catFloatRegister,
    catLParen,
    catRParen,
    catLBracket,
    catRBracket,
    catPlus,
    catMinus,
    catStar,
    catSlash,
    catSegmentOverride,
    catIntConst,
    catStringConst,
    catLabel,
    catLocalLabel,
    catPtr,
    catByte,
    catWord,
    catDWord,
    catPWord,
    catQWord,
    catTByte,
    catNear,
    catFar,
    catHIGH,
    catLOW,
    catOFFSET,
    catSEG,
    catTYPE,
    catMOD,
    catSHL,
    catSHR,
    catNOT,
    catAND,
    catOR,
    catXOR,
    catIdentifier,
    catColon,
    catSeparator,
    catComma,
    catEnd,
    catFuncResult,
    catPoint,
    catDB,
    catDW,
    catDD,
    catDQ,
    catDT,
    catRealConst,
    catEncodedRealConst
  );

  pBAsmCompiler = ^tBAsmCompiler;
  tBAsmCompiler = object( tScanner)
    CurLabel: LongInt;
    LastAsmToken: tAsmToken;
    FirstToken: Boolean;
    LastAsmOp: tAsmOp;
    LastRegister: tRegister;
    CurAsmBlock: Pointer;
    LabelPrefix: pString;
    function GetAsmToken: tAsmToken;
    function ReadAsmStatement: pCodeTree;
    function ReadAsmInstruction: pAsmInstruction;
    procedure ReadAsmExpression( var Operand: tOperand);
    procedure ReadAsmAdditive( var Operand: tOperand);
    procedure ReadAsmMultiple( var Operand: tOperand);
    procedure ReadAsmUnary( var Operand: tOperand);
    procedure ReadAsmNode( var Operand: tOperand);
    procedure AsmConsume( AsmToken: tAsmToken);
    procedure AddAsmExpression(var Dest, Source: tOperand);
    procedure DecodeOperand( var Op: tOperand);
    function FindLocalLabel( const Name: String): Boolean;
    procedure CheckOperand( Op: tOperand);
    function CreateInstruction( AsmOp: tAsmOp): Pointer;
    procedure CreateRecordOffset( var Operand: tOperand);
    function CreateLabel: String;
    function CreateDB: Pointer;
    function CreateDW: Pointer;
    function CreateDD: Pointer;
    function CreateDQ: Pointer;
    function CreateDT: Pointer;
  end;


const

  OperatorsCount = Ord(catXOR) - Ord( catPTR) + 1;

  AsmOperatorsNames: array [0..OperatorsCount - 1] of string[6] = (
    'PTR', 'BYTE', 'WORD', 'DWORD', 'PWORD', 'QWORD', 'TBYTE', 'NEAR', 'FAR',
    'HIGH', 'LOW', 'OFFSET', 'SEG', 'TYPE', 'MOD', 'SHL', 'SHR',
    'NOT', 'AND', 'OR', 'XOR'
  );

  PrefixesCount = 6;

  AsmPrefixes: array [0..PrefixesCount - 1] of tAsmOp = (
   caiREP, caiREPE, caiREPNE, caiREPE, caiREPNE, caiLOCK);

  AsmPrefixesName: array [0..PrefixesCount - 1] of String[5] = (
   'REP', 'REPE', 'REPNE', 'REPZ', 'REPNZ', 'LOCK');

  AsmDx: array [ 0..4] of String[ 2] = (
    'DB', 'DW', 'DD', 'DQ', 'DT'
  );


implementation

uses StdLib, Errors, Tools;

function IsPrefix( Line: String; var OpCode: tAsmOp): Boolean;
  var
    I: Integer;
  begin
    for I := 0 to PrefixesCount - 1 do
      if Line = AsmPrefixesName[I] then
        begin
          OpCode := AsmPrefixes[I];
          IsPrefix := True;
          Exit;
        end;
    IsPrefix := False;
  end;

function IsAsmInstruction( Line: String; var OpCode: tAsmOp): Boolean;
  var
    I: tAsmOp;
  begin
    for I := caiMOV to caiFADDS do
      if OpName[I] = Line then
        begin
          IsAsmInstruction := True;
          OpCode := I;
          Exit;
        end;
    IsAsmInstruction := False;
  end;

function IsRegister( Line: String; var Register: tRegister): Boolean;
  var
    I: tRegister;
  begin
    for I := crEAX to High( tRegister) do
      if Line = RegName[I] then
        begin
          IsRegister := True;
          Register := I;
          Exit;
        end;
    IsRegister := False;
  end;

function IsOperator( Line: String; var AsmToken: tAsmToken): Boolean;
  var
    I: Integer;
  begin
    for I := 0 to OperatorsCount - 1 do
      if Line = AsmOperatorsNames[I] then
        begin
          AsmToken := tAsmToken(Ord(catPtr) + I);
          IsOperator := True;
          Exit;
        end;
    IsOperator := False;
  end;

function IsDx( Line: String; var AsmToken: tAsmToken): Boolean;
  var
    I: Integer;
  begin
    for I := 0 to 4 do
      if Line = AsmDx[I] then
        begin
          AsmToken := tAsmToken(Ord(catDB) + I);
          IsDx := True;
          Exit;
        end;
    IsDx := False;
  end;

function IsKeyWord( Line: String; var AsmToken: tAsmToken;
    var AsmOp: tAsmOp; var Register: tRegister): Boolean;
  begin
    if IsPrefix( Line, AsmOp) then
      begin
        AsmToken := catPrefix;
        IsKeyWord := True;
        Exit;
      end;
    if IsAsmInstruction( Line, AsmOp) then
      begin
        AsmToken := catOpCode;
        IsKeyWord := True;
        Exit;
      end;
    if IsRegister( Line, Register) then
      begin
        if Register in [ crST..crST7 ] then
          AsmToken := catFloatRegister
        else
          AsmToken := catRegister;
        IsKeyWord := True;
        Exit;
      end;
    if IsOperator( Line, AsmToken) then
      begin
        IsKeyWord := True;
        Exit;
      end;
    if IsDx( Line, AsmToken) then
      begin
        IsKeyWord := True;
        Exit;
      end;
    if Line = '@RESULT' then
      begin
        IsKeyWord := True;
        AsmToken := catFuncResult;
        Exit;
      end;
    if Line = 'END' then
      begin
        IsKeyWord := True;
        AsmToken := catEnd;
        Exit;
      end;
    IsKeyWord := False;
  end;


function tBAsmCompiler.GetAsmToken: tAsmToken;
  var
    IsHex: Boolean;
  begin
    if CurChar = '{' then
      SkipComments;
    while CurChar in [' ', #9, #10, #13] do
      begin
        if CurChar = #13 then
          begin
            {Inc(CurLine);}
            NextChar;
            LastAsmToken := catSeparator;
            GetAsmToken := LastAsmToken;
            FirstToken := True;
            Exit;
          end;
        if NextChar{$IFDEF PPRO}(){$ENDIF} = '{' then
          SkipComments{$IFDEF PPRO}(){$ENDIF};
      end;
    Files^.PrevLine := Files^.CurLine;
    Files^.PrevCol := Files^.CurCol;
    if FirstToken then
      begin
        LastLine := '';
        LastAsmToken := catNone;
        FirstToken := False;
        if CurChar{$IFDEF PPRO}(){$ENDIF} = '@' then
          begin
            LastLine := CurChar{$IFDEF PPRO}(){$ENDIF};
            LastAsmToken := catLocalLabel;
            NextChar{$IFDEF PPRO}(){$ENDIF};
          end;

        while CurChar{$IFDEF PPRO}(){$ENDIF} in ['A'..'Z', 'a'..'z', '0'..'9', '_', '@'] do
          begin
            LastLine := LastLine + UpCase(CurChar{$IFDEF PPRO}(){$ENDIF});
            NextChar{$IFDEF PPRO}(){$ENDIF};
          end;
        if CurChar{$IFDEF PPRO}(){$ENDIF} = ':' then
          begin
            if LastAsmToken = catNone then
              LastAsmToken := catLabel;
            GetAsmToken := LastAsmToken;
            Exit;
          end;
        if IsKeyword(LastLine, LastAsmToken, LastAsmOp, LastRegister) then
          begin
            GetAsmToken := LastAsmToken;
            Exit;
          end;
      end
    else
      begin
        Files^.PrevCol :=  Files^.CurCol;
        Files^.PrevLine := Files^.CurLine;
        case CurChar{$IFDEF PPRO}(){$ENDIF} of

          ';':
            begin
              NextChar{$IFDEF PPRO}(){$ENDIF};
              LastLine := '';
              LastAsmToken := catSeparator;
              GetAsmToken := LastAsmToken;
              FirstToken := True;
            end;

          '@':
            begin
              LastLine := UpCase(CurChar{$IFDEF PPRO}(){$ENDIF});
              while NextChar{$IFDEF PPRO}(){$ENDIF} in ['A'..'Z', 'a'..'z', '0'..'9', '_', '@'] do
                begin
                  LastLine := LastLine + UpCase(CurChar{$IFDEF PPRO}(){$ENDIF});
                end;
              if LastLine = '@RESULT' then
                LastAsmToken := catFuncResult
              else
                LastAsmToken := catIdentifier;
              GetAsmToken := LastAsmToken;
              Exit;
            end;

          'a'..'z', 'A'..'Z', '_':
            begin
              LastLine := UpCase(CurChar{$IFDEF PPRO}(){$ENDIF});
              while NextChar{$IFDEF PPRO}(){$ENDIF} in ['A'..'Z', 'a'..'z', '0'..'9', '_'] do
                begin
                  LastLine := LastLine + UpCase(CurChar{$IFDEF PPRO}(){$ENDIF});
                end;
              if IsKeyWord(LastLine, LastAsmToken, LastAsmOp, LastRegister) then
                begin
                  GetAsmToken := LastAsmToken;
                  Exit;
                end;
              LastAsmToken := catIdentifier;
              GetAsmToken := LastAsmToken;
              Exit;
            end;

          '[':
            begin
              NextChar{$IFDEF PPRO}(){$ENDIF};
              LastLine := '[';
              LastAsmToken := catLBracket;
              GetAsmToken := LastAsmToken;
              Exit;
            end;

          ']':
            begin
              NextChar{$IFDEF PPRO}(){$ENDIF};
              LastLine := ']';
              LastAsmToken := catRBracket;
              GetAsmToken := LastAsmToken;
              Exit;
            end;

          '(':
            begin
              NextChar{$IFDEF PPRO}(){$ENDIF};
              LastLine := '(';
              LastAsmToken := catLParen;
              GetAsmToken := LastAsmToken;
              Exit;
            end;

          ')':
            begin
              NextChar{$IFDEF PPRO}(){$ENDIF};
              LastLine := ')';
              LastAsmToken := catRParen;
              GetAsmToken := LastAsmToken;
              Exit;
            end;

          '&':
            begin
              LastLine := '';
              while NextChar{$IFDEF PPRO}(){$ENDIF} in ['A'..'Z', 'a'..'z'] do
                LastLine := LastLine + UpCase( CurChar{$IFDEF PPRO}(){$ENDIF});
              LastAsmToken := catIdentifier;
              GetAsmToken := LastAsmToken;
              Exit;
            end;

          '*':
            begin
              NextChar{$IFDEF PPRO}(){$ENDIF};
              LastLine := '*';
              LastAsmToken := catStar;
              GetAsmToken := LastAsmToken;
              Exit;
            end;

          '/':
            begin
              NextChar{$IFDEF PPRO}(){$ENDIF};
              LastLine := '/';
              LastAsmToken := catSlash;
              GetAsmToken := LastAsmToken;
              Exit;
            end;

          '+':
            begin
              NextChar{$IFDEF PPRO}(){$ENDIF};
              LastLine := '+';
              LastAsmToken := catPlus;
              GetAsmToken := LastAsmToken;
              Exit;
            end;

          '-':
            begin
              NextChar{$IFDEF PPRO}(){$ENDIF};
              LastLine := '-';
              LastAsmToken := catMinus;
              GetAsmToken := LastAsmToken;
              Exit;
            end;

          '0'..'9':
            begin
              IsHex := False;
              LastLine := CurChar;
              while NextChar in [ 'A'..'F', 'a'..'f', '0'..'9' ] do
                begin
                  LastLine := LastLine + UpCase( CurChar);
                  if (LastLine[ Length( LastLine)] >= 'A') and
                    (LastLine[ Length( LastLine)] <= 'F') then
                    IsHex := True;
                end;
              case UpCase( CurChar) of
                'H':
                  begin
                    LastAsmToken := catIntConst;
                    LastLine := '$' + LastLine;
                    NextChar;
                  end;
                'R', 'r':
                  begin
                    LastAsmToken := catEncodedRealConst;
                    NextChar;
                  end;
                'E', '.':
                  begin
                    if IsHex then
                      Error( erErrorInRealConstant,
                        Files^.PrevLine, Files^.PrevCol, '');
                    if CurChar = '.' then
                      repeat
                        LastLine := LastLine + CurChar;
                      until (NextChar < '0') or (CurChar > '9');
                    if UpCase( CurChar) = 'E' then
                      LastLine := LastLine + UpCase( CurChar);
                      if (NextChar = '+') or (CurChar = '-') then
                        begin
                          LastLine := LastLine + CurChar;
                          NextChar;
                        end;
                      if (CurChar < '0') or (CurChar > '9') then
                        Error( erErrorInRealConstant,
                          Files^.PrevLine, Files^.PrevCol, '');
                      repeat
                        LastLine := LastLine + CurChar;
                      until (NextChar < '0') or (CurChar > '9');
                    LastAsmToken := catRealConst;
                  end;
                'A'..'Z':
                   Error( erErrorInIntegerConstant,
                     Files^.PrevLine, Files^.PrevCol, '');
                else
                  begin
                    if IsHex then
                      Error( erErrorInIntegerConstant,
                        Files^.PrevLine, Files^.PrevCol, '');
                    LastAsmToken := catIntConst;
                  end;
              end;
              GetAsmToken := LastAsmToken;
            end;
          '$':
            begin
              LastLine := '$';
              while NextChar{$IFDEF PPRO}(){$ENDIF} in [ '0'..'9', 'a'..'f', 'A'..'F' ] do
                LastLine := LastLine + UpCase(CurChar{$IFDEF PPRO}(){$ENDIF});
              LastAsmToken := catIntConst;
              GetAsmToken := LastAsmToken;
            end;
          ',':
            begin
              LastLine := ',';
              LastAsmToken := catComma;
              GetAsmToken := LastAsmToken;
              NextChar{$IFDEF PPRO}(){$ENDIF};
            end;
          '.':
            begin
              LastLine := '.';
              LastAsmToken := catPoint;
              GetAsmToken := LastAsmToken;
              NextChar{$IFDEF PPRO}(){$ENDIF};
            end;
          '''':
            begin
              LastLine := '';
              LastAsmToken := catStringConst;
              while NextChar{$IFDEF PPRO}(){$ENDIF} <> '''' do
                if (CurChar{$IFDEF PPRO}(){$ENDIF} in [#0, #13, #10]) then
                  Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '')
                else
                  LastLine := LastLine + CurChar{$IFDEF PPRO}(){$ENDIF};
              NextChar{$IFDEF PPRO}(){$ENDIF};
              GetAsmToken := LastAsmToken;
            end;
          ':':
            begin
              LastLine := ':';
              LastAsmToken := catColon;
              GetAsmToken := catColon;
              NextChar{$IFDEF PPRO}(){$ENDIF};
            end;
        end;
      end;
  end;

procedure tBAsmCompiler.CheckOperand( Op: tOperand);
  var
    LabName: pString;
  begin
    LabName := nil;
    case Op.Location of
      clSymbol:
        LabName := Op.LabelName;
      clMemory:
        LabName := Op.Reference.Symbol;
      clOffset:
        LabName := Op.LabelName;
    end;
    if Assigned( LabName) then
    if Assigned( LabName) and (Pos( '@', LabName^) > 0) then
      begin
        if not FindLocalLabel( LabName^) then
          Error( erUndefinedLabelInPrecedingStatement, Files^.CurLine, Files^.CurCol, '');
      end;
  end;

function tBAsmCompiler.ReadAsmStatement: pCodeTree;
  var
    AsmBlock: pProcAsm;
    AsmInstruction: pAsmInstruction;
    AsmCode: pAsmCode;
  begin
    {Consume( ctAsm);}
    LabelPrefix := NewStr( CreateLabel);
    FirstToken := True;
    GetAsmToken;
    AsmBlock := New( pProcAsm, Init);
    CurAsmBlock := AsmBlock;
    while LastAsmToken <> catEnd do
      begin
        while LastAsmToken = catSeparator do
          AsmConsume( catSeparator);
        if LastAsmToken = catEND then
          break;
        AsmInstruction := ReadAsmInstruction;
        AsmConsume( catSeparator);
        if Assigned( AsmInstruction) then
          AsmBlock^.Concat( AsmInstruction);
      end;
    AsmCode := AsmBlock^.First;
    while Assigned( AsmCode) do
      begin
        AsmInstruction := AsmCode^.Instruction;
        if Assigned( AsmInstruction) then
          begin
            CheckOperand( AsmInstruction^.Op1);
            CheckOperand( AsmInstruction^.Op2);
            CheckOperand( AsmInstruction^.Op3);
          end;
        AsmCode := AsmCode^.Next;
      end;
    NextToken;
    ReadAsmStatement := New( pCodeTree, CreateAsmBlock( AsmBlock));
    if Assigned( LabelPrefix) then
      DisposeStr( LabelPrefix);
    LabelPrefix := nil;
  end;

function tBasmCompiler.ReadAsmInstruction: pAsmInstruction;
  var
    LabelName: String;
    _AsmCode: pAsmInstruction;
    Prefix: tAsmOp;
    Symbol: pLabelSymbol;
  begin
    LabelName := '';
    if LastAsmToken in [catLabel, catLocalLabel] then
      begin
        if LastAsmToken = catLocalLabel then
          LabelName := LabelPrefix^ + LastLine
        else
          begin
            Symbol := CurrentFunction^.Func^.Definition^.LocalSymbols^.Search( LastLine);
            if not Assigned( Symbol) then
              Error( erUnknownIdentifier, Files^.PrevLine, Files^.PrevCol, LastLine);
            Symbol^.IsAssigned := True;
            LabelName := Symbol^.AsmName;
          end;
{writeln( '" ', lastasmtoken = catlocallabel, ' "');
writeln;}
        GetAsmToken;
        AsmConsume( catColon);
      end;
    _AsmCode := nil;
    Prefix := caiNoInstruction;
    if LastAsmToken = catPrefix then
      begin
        {AsmCode := New( pAsmInstruction, Create( LastAsmOp));
        GetAsmToken;}
        Prefix := LastAsmOp;
        AsmConsume( catPrefix);
      end;
    if (LastAsmToken <> catSeparator) and
      (LastAsmToken <> catEND) then
      begin
        case LastAsmToken of
          catDB:
            _AsmCode := CreateDB;
          catDW:
            _AsmCode := CreateDW;
          catDD:
            _AsmCode := CreateDD;
          catDQ:
            _AsmCode := CreateDQ;
          catDT:
            _AsmCode := CreateDT;
          else
            _AsmCode := CreateInstruction( LastAsmOp);
        end;
      end;
    {else if LastAsmToken <> catSeparator then
      Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');}
    if Assigned( _AsmCode) then
      _AsmCode^.Prefix := Prefix
    else
      _AsmCode := New( pAsmInstruction, Create( Prefix));
    if LabelName <> '' then
      _AsmCode^.LabelName := NewStr( LabelName);
{      ReadAsmInstruction := AsmCode
    else
      ReadAsmInstruction := pAsmInstruction( New( pLabeledInstruction,
        Create( LabelName, AsmCode)));}
    ReadAsmInstruction := _AsmCode
  end;

procedure tBasmCompiler.ReadAsmNode( var Operand: tOperand);
  var
    Op: tOperand;
    I: Integer;
    L: LongInt;
    Sym: pSymbol;
    Register: tRegister;
  begin
    case LastAsmToken of
      catLParen:
        begin
          AsmConsume( catLParen);
          ReadAsmExpression( Operand);
          AsmConsume( catRParen);
        end;
      catLBracket:
        begin
          repeat
            AsmConsume( catLBracket);
            Op.Location := clMemory;
            Op.Reference.Segment := crDefaultSeg;
            Op.Reference.Base := crNoRegister;
            Op.Reference.Index := crNoRegister;
            Op.Reference.Scale := 1;
            Op.Reference.Offset := 0;
            Op.Reference.Symbol := nil;
            Op.Reference.Size := csDefault;
            ReadAsmExpression( Op);
            AddAsmExpression( Operand, Op);
            AsmConsume( catRBracket);
          until LastAsmToken <> catLBracket;
          if LastAsmToken = catPoint then
            CreateRecordOffset( Operand);
        end;
      catRegister:
        begin
          if IsGeneralReg( LastRegister) then
            case Operand.Location of
              clNone:
                begin
                  Operand.Location := clRegister;
                  Operand.Register := LastRegister;
                end;
              clMemory:
                begin
                  if Operand.Reference.Base = crNoRegister then
                    Operand.Reference.Base := LastRegister
                  else if Operand.Reference.Index = crNoRegister then
                    begin
                      Operand.Reference.Index := LastRegister;
                      Operand.Reference.Scale := 1;
                    end
                  else
                    Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
                end;
              else
                Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
            end
          else if IsSegReg( LastRegister) then
            begin
              Register := LastRegister;
              AsmConsume( catRegister);
              if LastAsmToken = catColon then
                begin
                  AsmConsume( catColon);
                  ReadAsmNode( Operand);
                  if Operand.Location <> clMemory then
                    Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
                  Operand.Reference.Segment := Register;
                end
              else
                begin
                  if Operand.Location <> clNone then
                    Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
                  Operand.Location := clSegmentRegister;
                  Operand.Register := LastRegister;
                end;
              Exit;
            end
          else if IsFPUReg( LastRegister) then
            begin
              Operand.Location := clFPUStack;
              Operand.Register := LastRegister;
            end
          else if IsCRx( LastRegister) then
            begin
              Operand.Location := clCRx;
              Operand.Register := LastRegister;
            end;
          AsmConsume( catRegister);
        end;
      catFloatRegister:
        begin
          if Operand.Location <> clNone then
            Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
          Operand.Location := clFpuStack;
          Operand.Register := LastRegister;
          AsmConsume( catFloatRegister);
          if (LastRegister = crST) and (LastAsmToken = catLParen) then
            begin
              AsmConsume( catLParen);
              if (LastAsmToken <> catIntConst) or
                (LastLine[0] <> #1) or not (LastLine[1] in ['0'..'7']) then
                  Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
              Operand.Register := tRegister(Byte(crST0) +
                Byte(LastLine[1]) - Byte('0') );
              AsmConsume( catIntConst);
              AsmConsume( catRParen);
            end;
        end;
      catStringConst:
        begin
          case Length( LastLine) of
            1:
              L := Byte( LastLine[1]);
            2:
              L := Ord( LastLine[1]) + Ord( LastLine[2]) shl 8;
            3:
              L := Ord( LastLine[1]) + Ord( LastLine[2]) shl 8 + Ord( LastLine[3]) shl 8;
            4:
              L := Ord( LastLine[1]) + Ord( LastLine[2]) shl 8 +
                Ord( LastLine[3]) shl 8 + Ord( LastLine[4]) shl 8;
            else
              Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
          end;
          case Operand.Location of
            clImmediate:
              Inc( Operand.Value, L);
            clSymbol:
              Inc( Operand.Offset, L);
            clMemory:
              Inc( Operand.Reference.Offset, L);
            clNone:
              begin
                Operand.Location := clImmediate;
                Operand.Value := L;
                Operand.Size := csDefault;
              end;
            else
              Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
          end;
          GetAsmToken;
        end;
      catIntConst:
        begin
          Val( LastLine, L, I);
          case Operand.Location of
            clImmediate:
              Inc( Operand.Value, L);
            clSymbol:
              Inc( Operand.Offset, L);
            clMemory:
              Inc( Operand.Reference.Offset, L);
            clNone:
              begin
                Operand.Location := clImmediate;
                Operand.Value := L;
                Operand.Size := csDefault;
              end;
            else
              Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
          end;
          GetAsmToken;
        end;
      catFuncResult:
          begin
            Sym := FindLocalSymbol( FuncResultName);
            if not Assigned( Sym) then
              Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '')
            else
              begin
                if Operand.Location <> clNone then
                  Error( erErrorInAsmStatement,
                    Files^.PrevLine, Files^.PrevCol, '')
                else
                  begin
                    if pVariableSymbol(Sym)^.IsRegisterable then
                      begin
                        Operand.Location := clRegister;
                        Operand.Register := GetReg( pVariableSymbol( Sym)^.Register,
                          GetSize( pVariableSymbol(Sym)^.Definition^.GetSize));
                      end
                    else
                      begin
                        Operand.Location := clSymbol;
                        Operand.Offset := 0;
                        Operand.LabelName := NewStr( FuncResultName);
                        Operand.Size := csDefault;
                        Operand.Symbol := nil;
                      end;
                  end;
              end;
            GetAsmToken;
          end;
      catIdentifier:
        if Pos( '@', LastLine) = 0 then
          begin
            Sym := FindSymbol( LastLine, L);
            if not Assigned( Sym) then
              Error( erUnknownIdentifier, Files^.PrevLine, Files^.PrevCol, LastLine);
            case Sym^._Type of
              cConstSymbol:
                if pConstSymbol( Sym)^.ConstType^.DefType in [cOrdDefinition] then
                  begin
                    L := pConstSymbol( Sym)^.Value.IntValue;
                    case Operand.Location of
                      clImmediate:
                        Inc( Operand.Value, L);
                      clSymbol:
                        Inc( Operand.Offset, L);
                      clMemory:
                        Inc( Operand.Reference.Offset, L);
                      clNone:
                        begin
                          Operand.Location := clImmediate;
                          Operand.Value := L;
                          Operand.Size := csDefault;
                        end;
                      else
                        Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
                    end;
                  end
                else
                  Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
              cVariableSymbol,
              cTypedConstSymbol,
              cFunctionSymbol:
                begin
                  case Operand.Location of
                    clImmediate:
                      begin
                        Operand.Location := clSymbol;
                        Operand.Offset := Operand.Value;
                        Operand.LabelName := NewStr( LastLine);
                        Operand.Symbol := nil;
                      end;
                    clNone:
                      begin
                        Operand.Location := clSymbol;
                        Operand.Offset := 0;
                        Operand.LabelName := NewStr( LastLine);
                        Operand.Size := csDefault;
                        Operand.Symbol := nil;
                      end;
                    clMemory:
                      begin
                        if Assigned( Operand.Reference.Symbol) then
                          Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '')
                        else
                          Operand.Reference.Symbol := NewStr( LastLine);
                      end;
                  end;
                end;
              cTypeSymbol:
                if Assigned( pTypeSymbol( Sym)^.Definition) and
                  (pTypeSymbol( Sym)^.Definition^.DefType = cObjectDefinition) then
                  begin
                    GetAsmToken;
                    AsmConsume( catPoint);
                    if LastAsmToken <> catIdentifier then
                      Error( erMethodIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
                    Sym := pObjectDefinition( pTypeSymbol( Sym)^.Definition)^.PublicSymbols^.FindSymbol( LastLine);
                    if not Assigned( Sym) then
                      Error( erMethodIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
                    case Operand.Location of
                      clImmediate:
                        begin
                          Operand.Location := clSymbol;
                          Operand.Offset := Operand.Value;
                          Operand.LabelName := NewStr( Sym^.AsmName);
                          Operand.Symbol := nil;
                        end;
                      clNone:
                        begin
                          Operand.Location := clSymbol;
                          Operand.Offset := 0;
                          Operand.LabelName := NewStr( Sym^.AsmName);
                          Operand.Size := csDefault;
                          Operand.Symbol := nil;
                        end;
                    end;
                  end;
              else
                Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
            end;
            GetAsmToken;
          end
        else {if FindLocalLabel( LastLine) then}
          begin
            LastLine := LabelPrefix^ + LastLine;
            case Operand.Location of
              clImmediate:
                begin
                  Operand.Location := clSymbol;
                  Operand.Offset := Operand.Value;
                  Operand.LabelName := NewStr( LastLine);
                  Operand.Symbol := nil;
                end;
              clNone:
                begin
                  Operand.Location := clSymbol;
                  Operand.Offset := 0;
                  Operand.LabelName := NewStr( LastLine);
                  Operand.Size := csDefault;
                  Operand.Symbol := nil;
                end;
              clMemory:
                begin
                  if Assigned( Operand.Reference.Symbol) then
                    Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '')
                  else
                    Operand.Reference.Symbol := NewStr( LastLine);
                end;
              end;
            GetAsmToken;
          end;
    end;
  end;

procedure tBasmCompiler.ReadAsmUnary( var Operand: tOperand);
  var
    PrevToken: tAsmToken;
    Size: tSize;
  begin
    case LastAsmToken of
      catHIGH:
        begin
        end;
      catLOW:
        begin
        end;
      catPlus:
        begin
        end;
      catMinus:
        begin
        end;
      catColon:
        begin
        end;
      catOFFSET:
        begin
          AsmConsume( catOffset);
          ReadAsmNode( Operand);
          if Operand.Location <> clSymbol then
            Error( erIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
          Operand.Location := clOffset;
        end;
      catSEG:
        begin
        end;
      catTYPE:
        begin
        end;
      catBYTE, catWORD, catDWORD, catPWORD, catQWORD, catTBYTE, catNEAR, catFAR:
        begin
          PrevToken := LastAsmToken;
          {if GetAsmToken <> catPTR then
            Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol);}
          AsmConsume( LastAsmToken);
          AsmConsume( catPTR);
          ReadAsmNode( Operand);
          case PrevToken of
            catBYTE:
              Size := csBYTE;
            catWORD:
              Size := csWord;
            catDWord:
              Size := csDWord;
            catPWORD:
              Size := csPWORD;
            catQWord:
              Size := csQWord;
            catTByte:
              Size := csTByte;
            catFar:
              Size := csFar;
            catNear:
              Size := csNear;
            else
              Size := csDefault;
          end;
          case Operand.Location of
            clMemory:
              Operand.Reference.Size := Size;
            clSymbol, clImmediate:
              Operand.Size := Size;
          end;
        end;
      else
        ReadAsmNode( Operand);
    end;
  end;

procedure tBasmCompiler.ReadAsmMultiple( var Operand: tOperand);
  var
    Op1, Op2: tOperand;
  begin
    Op1.Location := clNone;
    ReadAsmUnary( Op1);
    while True do
      begin
        case LastAsmToken of
          catStar:
            begin
              AsmConsume( catStar);
              Op2.Location := clNone;
              ReadAsmUnary( Op2);
              case Op1.Location of
                clImmediate:
                  begin
                    if Op2.Location = clImmediate then
                      Op1.Value := Op1.Value * Op2.Value
                    else
                      Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
                  end;
                clRegister:
                  begin
                    if (Op2.Location = clImmediate) and
                      (Op2.Value in [1, 2, 4, 8]) and
                      (Operand.Location = clMemory) and
                      (Operand.Reference.Index = crNoRegister) then
                      begin
                        Operand.Reference.Index := Op1.Register;
                        Operand.Reference.Scale := Op2.Value;
                        Op1.Location := clNone;
                      end
                    else
                      Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
                  end;
                else
                  Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
              end;
            end;
          catSlash:
            begin
              AsmConsume( catSlash);
              Op2.Location := clNone;
              ReadAsmUnary( Op2);
              if (Op1.Location = clImmediate) and ( Op2.Location = clImmediate) then
                Op1.Value := Op1.Value div Op2.Value
              else
                Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
            end;
          catMOD:
            begin
              AsmConsume( catMOD);
              Op2.Location := clNone;
              ReadAsmUnary( Op2);
              if (Op1.Location = clImmediate) and ( Op2.Location = clImmediate) then
                Op1.Value := Op1.Value mod Op2.Value
              else
                Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
            end;
          catSHL:
            begin
              AsmConsume( catSHL);
              Op2.Location := clNone;
              ReadAsmUnary( Op2);
              if (Op1.Location = clImmediate) and ( Op2.Location = clImmediate) then
                Op1.Value := Op1.Value shl Op2.Value
              else
                Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
            end;
          catSHR:
            begin
              AsmConsume( catSHR);
              Op2.Location := clNone;
              ReadAsmUnary( Op2);
              if (Op1.Location = clImmediate) and ( Op2.Location = clImmediate) then
                Op1.Value := Op1.Value shr Op2.Value
              else
                Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
           end;
          else
            begin
              if (Op1.Location = clRegister) and (Operand.Location = clMemory) then
                begin
                  Op1.Location := clMemory;
                  Op1.Reference.Base := Op1.Register;
                  Op1.Reference.Segment := crDefaultSeg;
                  Op1.Reference.Index := crNoRegister;
                  Op1.Reference.Scale := 1;
                  Op1.Reference.Symbol := nil;
                  Op1.Reference.Offset := 0;
                  Op1.Reference.Size := csDefault;
                end;
              AddAsmExpression( Operand, Op1);
              Exit;
            end;
        end;
      end;
  end;

procedure tBasmCompiler.ReadAsmAdditive( var Operand: tOperand);
  var
    Op1, Op2: tOperand;
  begin
    Op1 := Operand;
    ReadAsmMultiple( Op1);
    while True do
      begin
        case LastAsmToken of
          catPlus:
            begin
              AsmConsume( catPlus);
              Op2 := Operand;
              ReadAsmMultiple( Op2);
              AddAsmExpression( Op1, Op2);
            end;
          catMinus:
            begin
              AsmConsume( catMinus);
              Op2.Location := clNone;
              ReadAsmMultiple( Op2);
              if Op2.Location = clImmediate then
                Op2.Value := -Op2.Value
              else
                Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
              AddAsmExpression( Op1, Op2);
            end;
          else
            begin
              Operand := Op1;
              Exit;
            end;
        end;
      end;
  end;

procedure tBasmCompiler.ReadAsmExpression( var Operand: tOperand);
  begin
    ReadAsmAdditive( Operand);
    while True do
      begin
        if LastAsmToken = catNot then
          begin
          end;
        case LastAsmToken of
          catAND:
            begin
            end;
          catOR:
            begin
            end;
          catXOR:
            begin
            end;
          else
            break;
        end;
      end;
  end;

procedure tBasmCompiler.AsmConsume( AsmToken: tAsmToken);
  var
   ErrorCode: LongInt;
  begin
    if AsmToken = LastAsmToken then
      GetAsmToken
    else
      begin
        case AsmToken of
          catLParen:
            ErrorCode := erLeftParenExpected;
          catRParen:
            ErrorCode := erRightParenExpected;
          catLBracket:
            ErrorCode := erLeftBracketExpected;
          catRBracket:
            ErrorCode := erRightBracketExpected;
          catOpCode:
            ErrorCode := erSyntaxError;
          else
            ErrorCode := erErrorInAsmStatement;
        end;
        Error( ErrorCode, Files^.PrevLine, Files^.PrevCol, '');
      end;
  end;

procedure tBasmCompiler.AddAsmExpression(var Dest, Source: tOperand);
  begin
    case Dest.Location of
      clImmediate:
        begin
          case Source.Location of
            clNone:;
            clImmediate:
              Inc( Dest.Value, Source.Value);
            clSymbol:
              begin
                Inc( Source.Offset, Dest.Value);
                Dest := Source;
              end;
            clMemory:
              begin
                Inc( Source.Reference.Offset, Dest.Value);
                Dest := Source;
              end;
            else
              Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
          end;
        end;
      clRegister:
          case Source.Location of
            clNone:;
            clMemory:
              begin
                if Source.Reference.Base = crNoRegister then
                  Source.Reference.Base := Dest.Register
                else
                  Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
                Dest := Source;
              end;
            else
              Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
          end;
      clSymbol:
        begin
          case Source.Location of
            clNone:;
            clImmediate:
              Inc( Dest.Offset, Source.Value);
            clMemory:
              begin
                if Assigned( Source.Reference.Symbol) then
                  Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '')
                else
                  begin
                    Source.Reference.Symbol := Dest.LabelName;
                    Dest := Source;
                  end;
              end;
            else
              Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
          end;
        end;
      clMemory:
        begin
          case Source.Location of
            clNone:;
            clImmediate:
              Inc( Dest.Reference.Offset, Source.Value);
            clSymbol:
              begin
                if not Assigned( Dest.Reference.Symbol) then
                  begin
                    Dest.Reference.Symbol := Source.LabelName;
                    Inc( Dest.Reference.Offset, Source.Offset);
                    Dest.Reference.Size := Source.Size;
                  end
                else
                  Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
              end;
            clMemory:
              begin
                if Assigned( Source.Reference.Symbol) then
                  if Assigned( Dest.Reference.Symbol) then
                    Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '')
                  else
                    Dest.Reference.Symbol := Source.Reference.Symbol;
                Inc( Dest.Reference.Offset, Source.Reference.Offset);
                if Source.Reference.Base <> crNoRegister then
                  begin
                    if Dest.Reference.Base = crNoRegister then
                      Dest.Reference.Base := Source.Reference.Base
                    else if Dest.Reference.Index = crNoRegister then
                      begin
                        Dest.Reference.Index := Source.Reference.Base;
                        Dest.Reference.Scale := 1;
                      end
                    else
                      Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
                  end;
                if Source.Reference.Index <> crNoRegister then
                  begin
                    if Dest.Reference.Index <> crNoRegister then
                      Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '')
                    else
                      begin
                        Dest.Reference.Index := Source.Reference.Index;
                        Dest.Reference.Scale := Source.Reference.Scale;
                      end;
                  end;
                if Source.Reference.Size <> csDefault then
                  if Dest.Reference.Size <> csDefault then
                    Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '')
                  else
                    Dest.Reference.Size := Source.Reference.Size;
              end;
            else
              Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
          end;
        end;
      clNone:
        Dest := Source;
    end;
  end;

procedure tBasmCompiler.DecodeOperand( var Op: tOperand);
  var
    SymName: pString;
    Sym: pSymbol;
    L: LongInt;
  begin
    SymName := nil;
    if Op.Location in [ clSymbol, clOffset] then
      SymName := Op.LabelName
    else if Op.Location = clMemory then
      SymName := Op.Reference.Symbol;
    Sym := nil;
    if Assigned( SymName) then
      begin
        if Pos( '$', SymName^) > 0 then Exit;
        Sym := FindSymbol( SymName^, L);
      end;
    if Assigned( Sym) then
      if ( Sym^._Type in [cVariableSymbol, cTypedConstSymbol]) and
        (Op.Location = clSymbol) and (Op.Offset = 0) then
        begin
          Op.Location := clMemory;
          Op.Reference.Size := Op.Size;
          Op.Reference.Segment := crDefaultSeg;
          Op.Reference.Base := crNoRegister;
          Op.Reference.Index := crNoRegister;
          Op.Reference.Scale := 1;
          Op.Reference.Symbol := SymName;
          Op.Reference.Offset := 0;
        end;
    case Op.Location of
      clMemory:
        begin
          if Assigned( Op.Reference.Symbol) then
            if Assigned( Sym) and ( Sym^._Type in [cVariableSymbol, cTypedConstSymbol]) then
              if not pVariableSymbol( Sym)^.IsRegisterable then
                begin
                  if Sym^.Owner^.SymbolTableType = stLocalTable then
                   begin
                      if Op.Reference.Base = crNoRegister then
                        Op.Reference.Base := crEBP
                      else if Op.Reference.Index = crNoRegister then
                        Op.Reference.Index := crEBP
                      else
                        Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
                      Inc( Op.Reference.Offset, pVariableSymbol( Sym)^.Offset);
                      Op.Reference.Symbol := nil;
                    end
                  else
                    Op.Reference.Symbol := NewStr( Sym^.AsmName);
                  DisposeStr( SymName);
                  if Op.Reference.Size = csDefault then
                    Op.Reference.Size := GetSize( pVariableSymbol(Sym)^.Size);
                end
              else
                begin
                  if (Op.Reference.Base <> crNoRegister) or
                    (Op.Reference.Index <> crNoRegister) then
                    Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevLine, '')
                  else
                    begin
                      DisposeStr( SymName);
                      Op.Location := clRegister;
                      Op.Register := GetReg( pVariableSymbol( Sym)^.Register,
                        GetSize( pVariableSymbol( Sym)^.Definition^.GetSize));
                    end;
                end
            else
              Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
        end;
      clSymbol,
      clOffset:
        if Assigned( Sym) then
          begin
            Op.Symbol := Sym;
            {DisposeStr( SymName);}
          end;
        {else
          Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol);}
    end;
  end;


function tBasmCompiler.FindLocalLabel( const Name: String): Boolean;
  var
    AsmCode: pAsmCode;
  begin
    FindLocalLabel := False;
    if Assigned( CurAsmBlock) then
      begin
        AsmCode := pProcAsm( CurAsmBlock)^.First;
        while Assigned( AsmCode) do
          begin
            if Assigned( AsmCode^.Instruction) and
              Assigned( AsmCode^.Instruction^.LabelName) and
              (AsmCode^.Instruction^.LabelName^ = Name) then
                begin
                  FindLocalLabel := True;
                  Exit;
                end;
            AsmCode := AsmCode^.Next;
          end;
      end;
  end;


function tBasmCompiler.CreateInstruction( AsmOp: tAsmOp): Pointer;
  var
    Op1, Op2, Op3: tOperand;
  begin
    {GetAsmToken;}
    AsmConsume( catOpCode);
    Op1.Location := clNone;
    Op2.Location := clNone;
    Op3.Location := clNone;
    if LastAsmToken <> catSeparator then
      begin
        ReadAsmExpression( Op1);
        DecodeOperand( Op1);
        if ( LastAsmToken = catComma) then
          begin
            AsmConsume( catComma);
            ReadAsmExpression( Op2);
            DecodeOperand( Op2);
            if ( LastAsmToken = catComma) then
              begin
                AsmConsume( catComma);
                ReadAsmExpression( Op3);
                DecodeOperand( Op3);
              end;
          end;
      end;

    if (FindInstruction( AsmOp, Op1, Op2, Op3) >= 0) and
      not ( (AsmOp = caiPOP) and (Op1.Location = clSegmentRegister) and
        (Op1.Register = crCS) ) then
      CreateInstruction := New( pAsmInstruction, CreateInstruction( AsmOp, @Op1, @Op2, @Op3))
    else
      begin
        Error( erInvalidCombinationOfOpcodeAndOperations,
          Files^.PrevLine, Files^.PrevCol, '');
        CreateInstruction := nil;
      end;
  end;

procedure tBasmCompiler.CreateRecordOffset( var Operand: tOperand);
  var
    SymTable: pSymbolTable;
    Symbol: pSymbol;
    L: LongInt;
  begin
    SymTable := nil;
    if Operand.Location = clMemory then
      begin
        AsmConsume( catPoint);
        if LastAsmToken <> catIdentifier then
          begin
            Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
            Exit;
          end;
        Symbol := FindSymbol( LastLine, L);
        if not Assigned( Symbol) or (Symbol^._Type <> cTypeSymbol) or
          not Assigned( pTypeSymbol( Symbol)^.Definition) then
          begin
            Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
            Exit;
          end;
        case pTypeSymbol( Symbol)^.Definition^.DefType of
          cRecordDefinition:
            SymTable := pRecordDefinition( pTypeSymbol( Symbol)^.Definition)^.Fields;
          cObjectDefinition:
            SymTable := pObjectDefinition( pTypeSymbol( Symbol)^.Definition)^.PublicSymbols;
        end;
        AsmConsume( catIdentifier);
        while LastAsmToken = catPoint do
          begin
            if not Assigned( SymTable) then
              begin
                Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
                Exit;
              end;
            AsmConsume( catPoint);
            if LastAsmToken = catIdentifier then
              begin
                Symbol := SymTable^.FindSymbol( LastLine);
                if not Assigned( Symbol) or (Symbol^._Type <> cVariableSymbol) or
                  ( pVariableSymbol( Symbol)^.VarType <> cvtField) or
                  not Assigned( pVariableSymbol( Symbol)^.Definition) then
                  begin
                    Error( erErrorInAsmStatement, Files^.PrevLine, Files^.PrevCol, '');
                    Exit;
                  end;
                Inc( Operand.Reference.Offset, pVariableSymbol( Symbol)^.Offset);
                Operand.Reference.Size :=
                  GetSize( pVariableSymbol( Symbol)^.Definition^.GetSize);
                if pVariableSymbol( Symbol)^.Definition^.DefType <> cRecordDefinition then
                  SymTable := nil
                else
                  SymTable := pRecordDefinition(
                    pVariableSymbol( Symbol)^.Definition)^.Fields;
              end;
            AsmConsume( catIdentifier);
          end;
      end;
  end;


function tBasmCompiler.CreateDB: Pointer;
  var
    Value: pDefineValue;
    Data: pByteArray;
    L: LongInt;
    Res: Integer;
  begin
    AsmConsume( catDB);
    New( Value);
    Value^.Data := nil;
    Value^.DataSize := 0;
    repeat
    case LastAsmToken of
      catStringConst:
        if Length( LastLine) > 0 then
          begin
            Data := Value^.Data;
            GetMem( Value^.Data, Value^.DataSize + Length( LastLine) );
            if Assigned( Data) then
              begin
                Move( Data^, Value^.Data^, Value^.DataSize);
                FreeMem( Data, Value^.DataSize);
              end;
            Move( LastLine[1], Value^.Data^[Value^.DataSize], Length( LastLine));
            Inc( Value^.DataSize, Length( LastLine));
          end;
      catIntConst:
        begin
          Data := Value^.Data;
          GetMem( Value^.Data, Value^.DataSize + 1 );
          Val( LastLine, L, Res);
          if (L < -128) or (L > 255) then
            Error( erConstantOutOfRange, Files^.PrevLine, Files^.PrevCol, LastLine);
          if Assigned( Data) then
            begin
              Move( Data^, Value^.Data^, Value^.DataSize);
              FreeMem( Data, Value^.DataSize);
            end;
          Value^.Data^[Value^.DataSize] := L;
          Inc( Value^.DataSize);
        end;
      else
        Error( erSyntaxError, Files^.PrevLine, Files^.PrevCol, '');
    end;
      if GetAsmToken <> catComma then break;
      AsmConsume( catComma);
    until True;
    CreateDB := New( pAsmInstruction, Create_DB( Value));
  end;

function tBasmCompiler.CreateDW: Pointer;
  var
    Value: pDefineValue;
    Data: pByteArray;
    L: LongInt;
    Res: Integer;
  begin
    AsmConsume( catDW);
    New( Value);
    Value^.Data := nil;
    Value^.DataSize := 0;
    repeat
      case LastAsmToken of
        catIntConst:
          begin
            Data := Value^.Data;
            GetMem( Value^.Data, Value^.DataSize + 2 );
            Val( LastLine, L, Res);
            if (L < -32768) or (L > 65535) then
              Error( erConstantOutOfRange, Files^.PrevLine, Files^.PrevCol, LastLine);
            if Assigned( Data) then
              begin
                Move( Data^, Value^.Data^, Value^.DataSize);
                FreeMem( Data, Value^.DataSize);
              end;
            Move( L, Value^.Data^[Value^.DataSize], 2);
            Inc( Value^.DataSize, 2);
          end;
        else
          Error( erSyntaxError, Files^.PrevLine, Files^.PrevCol, '');
      end;
      if GetAsmToken <> catComma then break;
      AsmConsume( catComma);
    until True;
    CreateDW := New( pAsmInstruction, Create_DB( Value));
  end;

function tBasmCompiler.CreateDD: Pointer;
  var
    Value: pDefineValue;
    Data: pByteArray;
    L: LongInt;
    R: Single;
    Res: Integer;
  begin
    AsmConsume( catDD);
    New( Value);
    Value^.Data := nil;
    Value^.DataSize := 0;
    repeat
      case LastAsmToken of
        catIntConst:
          begin
            Data := Value^.Data;
            GetMem( Value^.Data, Value^.DataSize + 4 );
            Val( LastLine, L, Res);
            if Assigned( Data) then
              begin
                Move( Data^, Value^.Data^, Value^.DataSize);
                FreeMem( Data, Value^.DataSize);
              end;
            Move( L, Value^.Data^[Value^.DataSize], 4);
            Inc( Value^.DataSize, 4);
          end;
        catRealConst:
          begin
            Data := Value^.Data;
            GetMem( Value^.Data, Value^.DataSize + 4 );
            Val( LastLine, R, Res);
            if Assigned( Data) then
              begin
                Move( Data^, Value^.Data^, Value^.DataSize);
                FreeMem( Data, Value^.DataSize);
              end;
            Move( R, Value^.Data^[Value^.DataSize], 4);
            Inc( Value^.DataSize, 4);
          end;
        catEncodedRealConst:
          begin
            Remove0( LastLine, 8);
            if Length( LastLine) <> 8 then
              Error( erErrorInRealConstant, Files^.PrevCol, Files^.PrevLine, '');
            Data := Value^.Data;
            GetMem( Value^.Data, Value^.DataSize + 4);
            if Assigned( Data) then
              begin
                Move( Data^, Value^.Data^, Value^.DataSize);
                FreeMem( Data, Value^.DataSize);
              end;
            DecodeRealConst( Value^.Data^[ Value^.DataSize], LastLine);
            Inc( Value^.DataSize, 4);
          end;
        else
          Error( erSyntaxError, Files^.PrevLine, Files^.PrevCol, '');
      end;
      if GetAsmToken <> catComma then break;
      AsmConsume( catComma);
    until True;
    CreateDD := New( pAsmInstruction, Create_DB( Value));
  end;

function tBasmCompiler.CreateDQ: Pointer;
  var
    Value: pDefineValue;
    Data: pByteArray;
    L: LongInt;
    R: Double;
    Res: Integer;
  begin
    AsmConsume( catDQ);
    New( Value);
    Value^.Data := nil;
    Value^.DataSize := 0;
    repeat
      case LastAsmToken of
        catIntConst:
          begin
            Data := Value^.Data;
            GetMem( Value^.Data, Value^.DataSize + 8 );
            Val( LastLine, L, Res);
            if Assigned( Data) then
              begin
                Move( Data^, Value^.Data^, Value^.DataSize);
                FreeMem( Data, Value^.DataSize);
              end;
            Move( L, Value^.Data^[Value^.DataSize], 4);
            FillChar( Value^.Data^[Value^.DataSize + 4], 4, 0);
            Inc( Value^.DataSize, 8);
          end;
        catRealConst:
          begin
            Data := Value^.Data;
            GetMem( Value^.Data, Value^.DataSize + 8);
            Val( LastLine, R, Res);
            if Assigned( Data) then
              begin
                Move( Data^, Value^.Data^, Value^.DataSize);
                FreeMem( Data, Value^.DataSize);
              end;
            Move( R, Value^.Data^[Value^.DataSize], 8);
            Inc( Value^.DataSize, 8);
          end;
        catEncodedRealConst:
          begin
            Remove0( LastLine, 16);
            if Length( LastLine) <> 16 then
              Error( erErrorInRealConstant, Files^.PrevCol, Files^.PrevLine, '');
            Data := Value^.Data;
            GetMem( Value^.Data, Value^.DataSize + 8);
            if Assigned( Data) then
              begin
                Move( Data^, Value^.Data^, Value^.DataSize);
                FreeMem( Data, Value^.DataSize);
              end;
            DecodeRealConst( Value^.Data^[ Value^.DataSize], LastLine);
            Inc( Value^.DataSize, 8);
          end;
        else
          Error( erSyntaxError, Files^.PrevLine, Files^.PrevCol, '');
      end;
      if GetAsmToken <> catComma then break;
      AsmConsume( catComma);
    until True;
    CreateDQ := New( pAsmInstruction, Create_DB( Value));
  end;

function tBasmCompiler.CreateDT: Pointer;
  var
    Value: pDefineValue;
    Data: pByteArray;
    L: LongInt;
    R: Extended;
    Res: Integer;
  begin
    AsmConsume( catDT);
    New( Value);
    Value^.Data := nil;
    Value^.DataSize := 0;
    repeat
      case LastAsmToken of
        catIntConst:
          begin
            Data := Value^.Data;
            GetMem( Value^.Data, Value^.DataSize + 10 );
            Val( LastLine, L, Res);
            if Assigned( Data) then
              begin
                Move( Data^, Value^.Data^, Value^.DataSize);
                FreeMem( Data, Value^.DataSize);
              end;
            Move( L, Value^.Data^[Value^.DataSize], 4);
            FillChar( Value^.Data^[Value^.DataSize + 4], 6, 0);
            Inc( Value^.DataSize, 10);
          end;
        catRealConst:
          begin
            Data := Value^.Data;
            GetMem( Value^.Data, Value^.DataSize + 10);
            Val( LastLine, R, Res);
            if Assigned( Data) then
              begin
                Move( Data^, Value^.Data^, Value^.DataSize);
                FreeMem( Data, Value^.DataSize);
              end;
            Move( R, Value^.Data^[Value^.DataSize], 10);
            Inc( Value^.DataSize, 10);
          end;
        catEncodedRealConst:
          begin
            Remove0( LastLine, 20);
            if Length( LastLine) <> 20 then
              Error( erErrorInRealConstant, Files^.PrevCol, Files^.PrevLine, '');
            Data := Value^.Data;
            GetMem( Value^.Data, Value^.DataSize + 10);
            if Assigned( Data) then
              begin
                Move( Data^, Value^.Data^, Value^.DataSize);
                FreeMem( Data, Value^.DataSize);
              end;
            DecodeRealConst( Value^.Data^[ Value^.DataSize], LastLine);
            Inc( Value^.DataSize, 10);
          end;
        else
          Error( erSyntaxError, Files^.PrevLine, Files^.PrevCol, '');
      end;
      if GetAsmToken <> catComma then break;
      AsmConsume( catComma);
    until True;
    CreateDT := New( pAsmInstruction, Create_DB( Value));
  end;

function tBasmCompiler.CreateLabel: String;
  begin
    CreateLabel := '$LABEL$' + ToStr( CurLabel);
    Inc( CurLabel);
  end;


end.