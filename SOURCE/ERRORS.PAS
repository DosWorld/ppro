{                    GNU GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Full text of license:
 https://www.gnu.org/licenses/gpl-3.0.en.html

 (c) Copyright 2022 DosWord
 (c) Copyright 1997-1998 Iggor Khachko - hachko@icl.kazan.su }

{
  Дата создания: 23.08.97
}

{$IFDEF TP}

{$X+,V-,G+,N+,E-,B-,T-}
{$IFDEF DEBUG}
{$I+,S+,R+,C+}
{$ELSE}
{$I-,S-,R-,C-}
{$ENDIF}

{$ENDIF}

unit Errors;

interface

uses Objects;

const

  erNoError                             = 0;
  erOutOfMemory                         = 1;
  erIdentifierExpected                  = 2;
  erUnknownIdentifier                   = 3;
  erDuplicateIdentifier                 = 4;
  erSyntaxError                         = 5;
  erErrorInRealConstant                 = 6;
  erErrorInIntegerConstant              = 7;
  erStringConstantExceedsLine           = 8;
  erUnexpectedEndOfFile                 = 10;
  erLineTooLong                         = 11;
  erTypeIdentifierExpected              = 12;
  erTooManyOpenFiles                    = 13;
  erInvalidFileName                     = 14;
  erFileNotFound                        = 15;
  erDiskFull                            = 16;
  erInvalidCompilerDirective            = 17;
  erTooManyFiles                        = 18;
  erUndefinedTypeInPointerDefinition    = 19;
  erVariableIdentifierExpected          = 20;
  erErrorInType                         = 21;
  erStructureTooLarge                   = 22;
  erSetBaseTypeOutOfRange               = 23;
  erInvalidFileComponent                = 24;
  erInvalidStringLength                 = 25;
  erTypeMismatch                        = 26;
  erInvalidSubrangeBaseType             = 27;
  erLowerBoundGreaterThanUpperBound     = 28;
  erOrdinalTypeExpected                 = 29;
  erIntegerConstantExpected             = 30;
  erConstantExpected                    = 31;
  erIntegerOrRealConstantExpected       = 32;
  erPointerTypeIdentifierExpected       = 33;
  erInvalidFunctionResultType           = 34;
  erLabelIdentifierExpected             = 35;
  erBEGINExpected                       = 36;
  erENDExpected                         = 37;
  erIntegerExpressionExpected           = 38;
  erOrdinalExpressionExpected           = 39;
  erBooleanExpressionExpected           = 40;
  erOperandTypesDoNotMatch              = 41;
  erErrorInExpression                   = 42;
  erIllegalAssignment                   = 43;
  erFieldIdentifierExpected             = 44;
  erObjectFileTooLarge                  = 45;
  erUndefinedExternal                   = 46;
  erInvalidObjectFileRecord             = 47;
  erCodeSegmentTooLarge                 = 48;
  erDataSegmentTooLarge                 = 49;
  erDOExpected                          = 50;
  erInvalidPUBLICDefinition             = 51;
  erInvalidEXTRNDefinition              = 52;
  erTooManyExtrnDefinitions             = 53;
  erOFExpected                          = 54;
  erINTERFACEExpected                   = 55;
  erInvalidRelocatableReference         = 56;
  erTHENExpected                        = 57;
  erTOorDOWNTOExpected                  = 58;
  erUndefinedForward                    = 59;
  erInvalidTypecast                     = 61;
  erDivisionByZero                      = 62;
  erInvalidFileType                     = 63;
  erCannotReadOrWriteVariableOfThisType = 64;
  erPointerVariableExpected             = 65;
  erStringVariableExpected              = 66;
  erStringExpressionExpected            = 67;
  erCircularUnitReference               = 68;
  erUnitNameMismatch                    = 69;
  erUnitVersionMismatch                 = 70;
  erInternalStackOverflow               = 71;
  erUnitFileFormatError                 = 72;
  erIMPLEMENTATIONExpected              = 73;
  erConstantAndCaseTypesDoNotMatch      = 74;
  erRecordOrObjectVariableExpected      = 75;
  erConstantOutOfRange                  = 76;
  erFileVariableExpected                = 77;
  erPointerExpressionExpected           = 78;
  erIntegerOrRealExpressionExpected     = 79;
  erLabelNotWithinCurrentBlock          = 80;
  erLabelAlreadyDefined                 = 81;
  erUndefinedLabelInPrecedingStatement  = 82;
  erInvalidATArgument                   = 83;
  erUNITExpected                        = 84;
  erSemicolonExpected                   = 85;
  erColonExpected                       = 86;
  erCommaExpected                       = 87;
  erLeftParenExpected                   = 88;
  erRightParenExpected                  = 89;
  erEqualExpected                       = 90;
  erAssignmentExpected                  = 91;
  erLeftBracketExpected                 = 92;
  erRightBracketExpected                = 93;
  erPointExpected                       = 94;
  erPointPointExpected                  = 95;
  erTooManyVariables                    = 96;
  erInvalidFORControlVariable           = 97;
  erIntegerVariableExpected             = 98;
  erFilesAndProcedureTypesAreNotAllowedHere = 99;
  erStringLengthMismatch                = 100;
  erInvalidOrderingOfFields             = 101;
  erStringConstantExpected              = 102;
  erIntegerOrRealVariableExpected       = 103;
  erOrdinalVariableExpected             = 104;
  erINLINEError                         = 105;
  erCharacterExpressionExpected         = 106;
  erTooManyRelocationItems              = 107;
  erOverflowInArithmenticOperation      = 108;
  erNoEnclosingCycleStatement           = 109;
  erDebugInformationTableOverflow       = 110;
  erCASEConstantOutOfRange              = 112;
  erErrorInStatement                    = 113;
  erCannotCallAnInterruptProcedure      = 114;
  erMustBeIn8087ModeToCompileThis       = 116;
  erTargetAddressNotFound               = 117;
  erIncludeFilesAreNotAllowedHere       = 118;
  erNoInheritedMethodsAreAccessibleHere = 119;
  erInvalidQualifier                    = 121;
  erInvalidVariableReference            = 122;
  erTooManySymbols                      = 123;
  erStatementPartTooLarge               = 124;
  erFilesMustBeVarParameters            = 126;
  erTooManyConditionalSymbols           = 127;
  erMisplacedConditionalDirective       = 128;
  erENDIFDirectiveMissing               = 129;
  erErrorInInitialConditionalDefines    = 130;
  erHeaderDoesNotMatchPreviousDefinition= 131;
  erCannotEvaluateThisExpression        = 133;
  erExpressionIncorrectlyTerminated     = 134;
  erInvalidFormatSpecifier              = 135;
  erInvalidInderectReference            = 136;
  erStructuredVariablesAreNotAllowedHere= 137;
  erCannotEvaluateWithoutSystemUnit     = 138;
  erCannotAccessThisSymbol              = 139;
  erInvalidFloatingPointOperation       = 140;
  erCannotCompileOverlaysToMemory       = 141;
  erPointerOrProceduralVariableExpected = 142;
  erInvalidProcedureOrFunctionReference = 143;
  erCannotOverlayThisUnit               = 144;
  erTooManyNestedScopes                 = 145;
  erFileAccessDenied                    = 146;
  erObjectTypeExpected                  = 147;
  erLocalObjectTypesAreNotAllowed       = 148;
  erVIRTUALExpected                     = 149;
  erMethodIdentifierExpected            = 150;
  erVirtualConstructorsAreNotAllowed    = 151;
  erConstructorIdentifierExpected       = 152;
  erDestructorIdentifierExpected        = 153;
  erFailOnlyAllowedWithinConstructors   = 154;
  erInvalidCombinationOfOpcodeAndOperations = 155;
  erMemoryReferenceExpected             = 156;
  erCannotAddOrSubstractRelocatableSymbols = 157;
  erInvalidRegisterCombination          = 158;
  er286_287InstructionsAreNotEnabled    = 159;
  erInvalidSymbolReference              = 160;
  erCodeGenerationError                 = 161;
  erASMExpected                         = 162;
  erDuplicateDynamicMethodIndex         = 163;
  erDuplicateResourceIdentifier         = 164;
  erDuplicateOrInvalidExportIndex       = 165;
  erProcedureOrFunctionIdenetifierExpected = 166;
  erCannotExportThisSymbol              = 167;
  erDuplicateExportName                 = 168;
  erExecutableFileHeaderTooLarge        = 169;
  erTooManySegments                     = 170;
  erCannotFindThisOperator              = 171;
  erInvalidFunctionParameters           = 172;
  erOverloadedFunctionWithSamesParameters = 173;
  erErrorInAsmStatement                 = 174;
  erUnknownOperator                     = 175;
  erAliasAlreadyDefined                 = 176;
  erFunctionResultTypeMismatch          = 177;
  erObjectsMustBeVarParameters          = 178;
  erErrorDirective                      = 179;

  erDoesNotImplemented                  = 254;
  erInternalError                       = 255;


  ErrorFileName = 'ERRORS';
  DefaultErrorFile = ErrorFileName + '.RUS';

procedure Error(ErrMsg: String);

function GetErrorMessage( Error: Integer): String;

procedure LoadErrorFile( const FileName: String);

implementation

uses Compiler;

const
  MaxError = 255;

type
  tMessArray = array [0..MaxError] of pString;
  pMessArray = ^tMessArray;

const
  ErrorMessages: pMessArray = nil;

var
  OldExitProc: Pointer;

function GetErrorMessage( Error: Integer): String;
  begin
    if (Error >= 0) and (Error <= MaxError) and Assigned( ErrorMessages) and
      Assigned( ErrorMessages^[Error]) then
      GetErrorMessage := ErrorMessages^[ Error]^
    else
      GetErrorMessage := 'Неизвестная ошибка';
  end;

procedure Error(ErrMsg: String);
  begin
    WriteLn('Error: ' + ErrMsg);
  end;

function HeapErrorHandler( Size: Word): Integer; {$IFDEF TP}far;{$ENDIF}
  begin
    if Size <> 0 then
      if Assigned( CurCompiler) then
        CurCompiler^.Error( erOutOfMemory, CurCompiler^.Files^.PrevLine,
          CurCompiler^.Files^.PrevCol, '');
  end;

procedure ExitClean; {$IFDEF TP}far;{$ENDIF}
  var
    I: LongInt;
  begin
    ExitProc := OldExitProc;
    if Assigned( ErrorMessages) then
      begin
        for I := 0 to MaxError do
          if Assigned( ErrorMessages^[I]) then
            DisposeStr( ErrorMessages^[I]);
        Dispose( ErrorMessages);
        ErrorMessages := nil;
      end;
{$IFDEF DEBUG}
    if Assigned( CurCompiler) then
      WriteLn( CurCompiler^.Files^.FileName,
        CurCompiler^.Files^.PrevLine: 10,
        CurCompiler^.Files^.PrevCol: 10, '   ');
{$ENDIF}
  end;


procedure LoadErrorFile( const FileName: String);
  var
    T: Text;
    I: LongInt;
    S: String;
  begin
    Assign( T, FileName);
    Reset( T);
    for I := 0 to MaxError do
      begin
        ReadLn( T, S);
        if Assigned( ErrorMessages^[I]) then
          DisposeStr( ErrorMessages^[I]);
        ErrorMessages^[I] := NewStr( S);
      end;
  end;


begin
  HeapError := @HeapErrorHandler;
  OldExitProc := ExitProc;
  ExitProc := @ExitClean;
  New( ErrorMessages);
  FillChar( ErrorMessages^, SizeOf( ErrorMessages^), 0);
  {LoadErrorFile( DefaultErrorFile);}
end.
