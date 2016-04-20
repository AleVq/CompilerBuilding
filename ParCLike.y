-- This Happy file was machine-generated by the BNF converter
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module ParCLike where
import AbsCLike
import LexCLike
import ErrM

}

%name pProgram Program
%name pStmtDecl StmtDecl
%name pRExpr RExpr
%name pLExpr LExpr
-- no lexer declaration
%monad { Err } { thenM } { returnM }
%tokentype {Token}
%token
  '!' { PT _ (TS _ 1) }
  '!=' { PT _ (TS _ 2) }
  '%' { PT _ (TS _ 3) }
  '&' { PT _ (TS _ 4) }
  '&&' { PT _ (TS _ 5) }
  '&=' { PT _ (TS _ 6) }
  '(' { PT _ (TS _ 7) }
  ')' { PT _ (TS _ 8) }
  '*' { PT _ (TS _ 9) }
  '*=' { PT _ (TS _ 10) }
  '+' { PT _ (TS _ 11) }
  '++' { PT _ (TS _ 12) }
  '+=' { PT _ (TS _ 13) }
  ',' { PT _ (TS _ 14) }
  '-' { PT _ (TS _ 15) }
  '--' { PT _ (TS _ 16) }
  '-=' { PT _ (TS _ 17) }
  '/' { PT _ (TS _ 18) }
  '/=' { PT _ (TS _ 19) }
  ';' { PT _ (TS _ 20) }
  '<' { PT _ (TS _ 21) }
  '<=' { PT _ (TS _ 22) }
  '=' { PT _ (TS _ 23) }
  '==' { PT _ (TS _ 24) }
  '>' { PT _ (TS _ 25) }
  '>=' { PT _ (TS _ 26) }
  'False' { PT _ (TS _ 27) }
  'True' { PT _ (TS _ 28) }
  '[' { PT _ (TS _ 29) }
  ']' { PT _ (TS _ 30) }
  '^' { PT _ (TS _ 31) }
  '^=' { PT _ (TS _ 32) }
  'bool' { PT _ (TS _ 33) }
  'break' { PT _ (TS _ 34) }
  'char' { PT _ (TS _ 35) }
  'const' { PT _ (TS _ 36) }
  'continue' { PT _ (TS _ 37) }
  'do' { PT _ (TS _ 38) }
  'else' { PT _ (TS _ 39) }
  'float' { PT _ (TS _ 40) }
  'for' { PT _ (TS _ 41) }
  'if' { PT _ (TS _ 42) }
  'int' { PT _ (TS _ 43) }
  'name' { PT _ (TS _ 44) }
  'ref' { PT _ (TS _ 45) }
  'res' { PT _ (TS _ 46) }
  'return' { PT _ (TS _ 47) }
  'val' { PT _ (TS _ 48) }
  'valres' { PT _ (TS _ 49) }
  'void' { PT _ (TS _ 50) }
  'while' { PT _ (TS _ 51) }
  '{' { PT _ (TS _ 52) }
  '|=' { PT _ (TS _ 53) }
  '||' { PT _ (TS _ 54) }
  '}' { PT _ (TS _ 55) }
  '\\' {PT _ (TS _ 56)}

L_integ  { PT _ (TI $$) }
L_charac { PT _ (TC $$) }
L_quoted { PT _ (TL $$) }
L_doubl  { PT _ (TD $$) }
L_ident  { PT _ (TV $$) }

%left '||'
%left '&&'
%left '!'
%nonassoc '==' '!=' '<' '<=' '>' '>='
%left '+' '-'
%left '*' '/' '%'
%right '^'
%left NEG
%left NO_ELSE
%nonassoc else

%%

Integer :: { Integer } : L_integ  { (read ( $1)) :: Integer }
Char    :: { Char }    : L_charac { (read ( $1)) :: Char }
Double  :: { Double }  : L_doubl  { (read ( $1)) :: Double }
Ident   :: { Ident }   : L_ident  { Ident $1 }

Boolean :: { Boolean }
Boolean : 'True' { Boolean_True }
        | 'False' { Boolean_False }

RExpr :: { RExpr }
      :  '(' RExpr ')'   { $2 }
      | RExpr '||' RExpr { InfixOp (BoolOp Or)   $1 $3 }
      | RExpr '&&' RExpr { InfixOp (BoolOp And)  $1 $3 }
      | RExpr '==' RExpr { InfixOp (RelOp Eq)    $1 $3 }
      | RExpr '!=' RExpr { InfixOp (RelOp Neq)   $1 $3 }
      | RExpr '<'  RExpr { InfixOp (RelOp Lt)    $1 $3 }
      | RExpr '<=' RExpr { InfixOp (RelOp LtE)   $1 $3 }
      | RExpr '>'  RExpr { InfixOp (RelOp Gt)    $1 $3 }
      | RExpr '>=' RExpr { InfixOp (RelOp GtE)   $1 $3 }
      | RExpr '+'  RExpr { InfixOp (ArithOp Add) $1 $3 }
      | RExpr '-'  RExpr { InfixOp (ArithOp Sub) $1 $3 }
      | RExpr '*'  RExpr { InfixOp (ArithOp Mul) $1 $3 }
      | RExpr '/'  RExpr { InfixOp (ArithOp Div) $1 $3 }
      | RExpr '%'  RExpr { InfixOp (ArithOp Mod) $1 $3 }
      | RExpr '^'  RExpr { InfixOp (ArithOp Pow) $1 $3 }
      | '!' RExpr        { UnaryOp Not $2 }
      | '-' RExpr %prec NEG { UnaryOp Neg $2 }
      | LExpr            { Lexpr $1 }
      | Ident '(' ListRExpr ')' { FCall $1 $3 }
      | Integer          { Int $1 }
      | Char             { Char $1 }
      | Double           { Double  $1}
      | Boolean          { Bool $1 }

FunCall :: { FunCall }
FunCall : Ident '(' ListRExpr ')' { Call $1 $3 }

ListRExpr :: { [RExpr] }
ListRExpr : {- empty -} { [] }
          | RExpr { (:[]) $1 }
          | RExpr ',' ListRExpr { (:) $1 $3 }

LExpr :: { LExpr }
LExpr : LExpr1 { $1 }
      | '*' RExpr { Deref $2 }
      | '++' LExpr1 { PrePostIncDecr Pre Inc $2 }
      | '--' LExpr1 { PrePostIncDecr Pre Decr $2 }

LExpr1 :: { LExpr }
LExpr1 : LExpr2 { $1 }
       | LExpr2 '++' { PrePostIncDecr Post Inc $1 }
       | LExpr2 '--' { PrePostIncDecr Post Decr $1 }

LExpr2 :: { LExpr }
LExpr2 : '(' LExpr ')' { $2 } | BLExpr { BasLExpr $1 }

BLExpr :: { BLExpr }
BLExpr : BLExpr '[' RExpr ']' { ArrayEl $1 $3 }
       | Ident { Id $1 }

Program :: { Program }
Program : ListDecl { Prog $1 }

ListDecl :: { [Decl] }
ListDecl : {- empty -} { [] } | ListDecl Decl { flip (:) $1 $2 }

Decl :: { Decl }
Decl : Type ListVarDeclInit ';' {Dvar $1 $2 }
     | Type ListIdent ';' { UndVar $1 $2 }
     | Type Ident '(' ListParameter ')' ListStmtDecl { Dfun $1 $2 $4 $6 }

ListVarDeclInit :: { [VarDeclInit] }
ListVarDeclInit : VarDeclInit { (:[]) $1 }
                | VarDeclInit ',' ListVarDeclInit { (:) $1 $3 }

ListIdent :: { [Ident] }
ListIdent : Ident { (:[]) $1 }
           | Ident ',' ListIdent { (:) $1 $3}

ListStmtDecl :: { [StmtDecl] }
ListStmtDecl : StmtDecl { (:[]) $1}
ListStmtDecl : StmtDecl ',' ListStmtDecl { (:) $1 $3 }

Type :: { Type }
Type : Type '[' Integer ']' { ArrDef $1 $3 }
     | Type '*' { Pointer $1}
     | 'bool' { Boolean }
     | 'char' { T_Char }
     | 'float' { T_Float }
     | 'int' { T_Int }
     | 'void' { T_Void }

VarDeclInit :: { VarDeclInit }
VarDeclInit : Ident '=' ComplexRExpr { VarDeclIn $1 $3 }

ComplexRExpr :: { ComplexRExpr }
ComplexRExpr : RExpr { Simple $1 }
             | '{' ListComplexRExpr '}' { Array $2 }

ListComplexRExpr :: { [ComplexRExpr] }
ListComplexRExpr : ComplexRExpr { (:[]) $1 }
                 | ComplexRExpr ',' ListComplexRExpr { (:) $1 $3 }

ListParameter :: { [Parameter] }
ListParameter : {- empty -} { [] }
              | Parameter { (:[]) $1 }
              | Parameter ',' ListParameter { (:) $1 $3 }

Parameter :: { Parameter }
Parameter : Modality Type Ident { Param $1 $2 $3 }

Modality :: { Modality }
Modality : {- empty -} { M_Void }
         | 'val' { M_Val }
         | 'ref' {  M_Ref }
         | 'const' {  M_Const }
         | 'res' {  M_Res }
         | 'valres' {  M_Valres }
         | 'name' {  M_Name }

StmtDecl :: { StmtDecl }
StmtDecl : Decl {  Decls $1 } | Stmt {  Stmts $1 }

ListStmt :: { [Stmt] }
ListStmt : {- empty -} { [] } | ListStmt Stmt { flip (:) $1 $2 }

Stmt :: { Stmt }
Stmt : FunCall ';' {  ProcCall $1 }
     | '{' ListStmtDecl '}' {  BlockDecl $2 }
     | JumpStmt ';' {  Jmp $1 }
     | IterStmt {  Iter $1 }
     | SelectionStmt {  Sel $1 }
     | LExpr Assignment_op RExpr ';' {  Assgn $1 $2 $3 }
     | LExpr ';' {  LExprStmt $1 }

Assignment_op :: { Assignment_op }
Assignment_op : '=' {  Assign }
              | '*=' {  AssgnMul }
              | '+=' {  AssgnAdd }
              | '/=' {  AssgnDiv }
              | '-=' {  AssgnSub }
              | '^=' {  AssgnPow }
              | '&=' {  AssgnAnd }
              | '|=' {  AssgnOr }

JumpStmt :: { JumpStmt }
JumpStmt : 'break' {  Break }
         | 'continue' {  Continue }
         | 'return' {  RetExpVoid }
         | 'return' '(' RExpr ')' {  RetExp $3 }

SelectionStmt :: { SelectionStmt }
SelectionStmt : 'if' '(' RExpr ')' ListStmtDecl {  IfNoElse $3 $5 }
              | 'if' '(' RExpr ')' ListStmtDecl 'else' ListStmtDecl {  IfElse $3 $5 $7 }

IterStmt :: { IterStmt }
IterStmt : 'while' '(' RExpr ')' ListStmtDecl {  While $3 $5 }
         | 'do' ListStmtDecl 'while' '(' RExpr ')' ';' {  DoWhile $2 $5 }
         | 'for' '(' Stmt ';' RExpr ';' Stmt ')' ListStmtDecl {  For $3 $5 $7 $9 }
{

returnM :: a -> Err a
returnM = return

thenM :: Err a -> (a -> Err b) -> Err b
thenM = (>>=)

happyError :: [Token] -> Err a
happyError ts =
  Bad $ "syntax error at " ++ tokenPos ts ++ 
  case ts of
    [] -> []
    [Err _] -> " due to lexer error"
    t:_ -> " before `" ++ id(prToken t) ++ "'"

myLexer = tokens
}

