-- copyright FEDERICO BALDO, ALESSANDRO VASQUEZ, ALESSANDRO BURIGANA

module TypeChecker where

import AbsCLike
import ErrM
import Control.Monad

type Fun = (Ident, (Type, [(Type, Modality)]))
type Var = (Ident, (Type, Def))
{- Def ci dice se la variabile è definita -}
type Def = Bool

type Env = [([Fun], [Var])]

{- enviroment iniziale con funzioni di default -}
bEnv = [([((Ident "writeInt"), (T_Void, [(T_Int, M_Ref)]))
		 ,((Ident "writeFloat"), (T_Void, [(T_Float, M_Ref)]))
		 ,((Ident "writeChar"), (T_Void, [(T_Char, M_Ref)]))
		 ,((Ident "readInt"), (T_Int, []))
		 ,((Ident "readFloat"), ( T_Float, []))
		 ,((Ident "readChar"), (T_Char, []))], [])]

typechecker :: Program -> Err Env
typechecker (Prog []) = Ok bEnv
typechecker (Prog decls) = 
	do
		{- aggiungiamo prima le dichiarazioni di funzione all'enviroment -}
		env <- checkDsFun bEnv decls
		checkDecls bEnv decls 

addScope :: Env -> Err Env 
addScope env = Ok ( ([],[]) : env )

remScope :: Env -> Err Env
remScope [] = Bad ("erroe\n")
remScope (scope:scopes) = Ok scopes

addVar :: Env -> Ident -> Type -> Def -> Err Env
addVar (scope:scopes) id typ def = 
	{- verifica anche che all'interno dello stesso scope non sia stata definita già la variabile -}
	case lookup id (snd scope) of 
		Nothing -> Ok ((fst scope, (id, (typ, def)) : (snd scope)) : scopes)
		Just _ -> Bad ("errore\n") -- già definita
	

{- la lista di dichiarazioni di variabile o è tutta definita o tutta indefinita -}
addVars :: Env -> [Ident] -> Type -> Def -> Err Env
addVars env [] _ _ = Ok env
addVars env (id:ids) typ def =
	do
		env_ <- addVar env id typ def
		addVars env_ ids typ def


addFun :: Env -> Ident -> Type -> [Parameter] -> Err Env
addFun env@(scope:scopes) id typ param = 
	case lookup id (fst scope) of
		Nothing ->
			do 
				env2 <- addScope env -- enviroment della funzione 
				{- add parameters -}
				env3 <- foldM (\env (Param mod typ id) -> addVar env id typ False) env2 param

				let sig = (typ, map (\(Param mod typ id) -> (typ, mod)) param)

				Ok ((\(scope1:scope2:scopes) -> scope1:((id, sig):fst scope, snd scope):scopes) env3)

		Just _ -> Bad("errore\n")

checkDsFun :: Env -> [Decl] -> Err Env
checkDsFun env [] = Ok env
checkDsFun env (dfun:dsfun) = 
	do
		env_ <- checkDFun env dfun
		checkDsFun env_ dsfun

checkDFun :: Env -> Decl -> Err Env
checkDFun env dfun =
	case dfun of 
		Dfun typ id param _ -> addFun env id typ param

checkDecls :: Env -> [Decl] -> Err Env --TODO tipo di ritorno
checkDecls env [] = Ok env
checkDecls env (decl:decls) =
	case decl of
		Dvar typ vdecls -> 
			do 
				env_ <- checkVarInit env vdecls typ
				checkDecls env_ decls
		UndVar typ id -> 
			do 
				env_ <- addVars env id typ False -- variabili indefinite
				checkDecls env_ decls
		Dfun typ _ _ stmts_decls ->
				do 
					checkStmtsDecls env stmts_decls typ 
					env_ <- remScope env
					checkDecls env decls
		_ -> Bad ("Bad Typing son of a bitch\n")

checkVarInit :: Env -> [VarDeclInit] -> Type -> Err Env
checkVarInit env [] _ = Ok env
checkVarInit env (vari:varis) typ = 
	case (\(VarDeclIn id crexpr) -> crexpr) vari of
		Simple rexpr -> 
					case (checkRExpr env rexpr) of
						Ok t ->
							if t == typ then
								do 
									env_ <- addVar env ((\(VarDeclIn id _) -> id) vari) typ True
									checkVarInit env_ varis typ 
							else 
									Bad ("Bad Typing son of a bitch\n")
						_ -> Bad ("Bad Typing son of a bitch\n")
		Array crexpr ->
					case checkCompRExpr env typ crexpr of
						Ok _ ->
							do 
								env_ <- addVar env ((\(VarDeclIn id _) -> id) vari) (ArrDef typ (length crexpr)) True
								checkVarInit env_ varis typ
						_  -> Bad ("Bad Typing son of a bitch\n")
		_ -> Bad ("Bad Typing son of a bitch\n")

checkCompRExpr :: Env -> Type -> [ComplexRExpr] -> Err Type
checkCompRExpr [] _ _ = Bad ("Bad Typing son of a bitch\n")
checkCompRExpr _ typ [] = Ok typ
checkCompRExpr env typ (crexpr:crexprs) = 
	case crexpr of
		Simple rexpr -> 
			case checkRExpr env rexpr of
				Ok t ->
					if ( typ == t ) then 
						checkCompRExpr env typ crexprs
					else 
						Bad ("Bad Typing son of a bitch\n")
				_ -> Bad ("Bad Typing son of a bitch\n")
		Array crexpr -> 
			do 
				checkCompRExpr env typ crexpr
				checkCompRExpr env typ crexprs
		_ -> Bad ("Bad Typing son of a bitch\n")


checkStmtsDecls :: Env -> [StmtDecl] -> Type -> Err Env
checkStmtsDecls env [] _  = Ok env
checkStmtsDecls env (st_de:sts_des) typ = -- typ è il tipo della funzione per controllare il return stmt
	case st_de of
		Decls decl -> 
			do 
				env_ <- checkDecls env (decl : [])
				checkStmtsDecls env_ sts_des typ
		Stmts stmt -> 
			case checkStmt env stmt typ of
				Ok _ -> checkStmtsDecls env sts_des typ
				_ -> Bad ("Bad Typing son of a bitch\n")


checkStmt :: Env -> Stmt -> Type -> Err Env
checkStmt env stmt typ =
	case stmt of
		Jmp jmpstmt ->
			case jmpstmt of	
				RetExpVoid -> case typ of
					T_Void -> Ok env
					_ -> Bad ("bad typing\n")
				RetExp rexpr -> 
					case checkRExpr env rexpr of
						Ok T_Float ->
							case typ of
			 					T_Float -> Ok env
			 					T_Int -> Ok env
			 					T_Char -> Ok env
			 					_ -> Bad ("Bad typing\n")
			 			Ok T_Int -> 
			 				case typ of
			 					T_Int -> Ok env 
			 					T_Char -> Ok env
			 					_ -> Bad ("Bad typing\n")
						Ok T_Char -> 
							case typ of
								T_Char -> Ok env
								T_Int -> Ok env
						_ -> Bad ("Bad typing\n")
				Break -> Ok env
				Continue -> Ok env 
		Assgn lexpr _ rexpr -> 
			case checkLExpr env lexpr of
				Ok T_Float ->
					case checkRExpr env rexpr of
	 					Ok T_Float -> Ok env
	 					Ok T_Int -> Ok env
	 					Ok T_Char -> Ok env
	 					_ -> Bad ("Bad typing\n")
	 			Ok T_Int -> 
	 				case checkRExpr env rexpr of
	 					Ok T_Int -> Ok env 
	 					Ok T_Char -> Ok env
	 					_ -> Bad ("Bad typing\n")
				Ok T_Char -> 
					case checkRExpr env rexpr of
						Ok T_Char -> Ok env
						Ok T_Int -> Ok env
				_ -> Bad ("Bad typing\n")
		Sel selstmt ->
			case selstmt of
				IfNoElse rexpr sts_des -> 
					case checkRExpr env rexpr of
						Ok Boolean -> checkStmtsDecls env sts_des typ
						_ -> Bad ("Bad typing\n")
				IfElse rexpr st1_de1 st2_de2 ->
					case checkRExpr env rexpr of
						Ok Boolean -> checkStmtsDecls env (st1_de1++st2_de2) typ
						_ -> Bad ("Bad Typing\n")
		Iter itrstmt ->
			case itrstmt of
				While rexpr sts_des -> 
					case checkRExpr env rexpr of
						Ok Boolean -> checkStmtsDecls env sts_des typ
						_ -> Bad ("Bad typing\n")
				DoWhile sts_des rexpr ->
					case checkRExpr env rexpr of
						Ok Boolean -> checkStmtsDecls env sts_des typ
						_ -> Bad ("Bad typing\n")
				For stmt1 rexpr stmt2 sts_des ->
					case checkStmt env stmt1 typ of
						Ok env -> 
							case checkRExpr env rexpr of
								Ok Boolean -> 
									case checkStmt env stmt2 typ of
										Ok env -> checkStmtsDecls env sts_des typ
										_ -> Bad ("Bad typeing\n")
								_ -> Bad ("Bad typeing\n")
						_ -> Bad ("Bad typeing\n")
		BlockDecl sts_des -> checkStmtsDecls env sts_des typ
		ProcCall funcall ->
			case funcall of
				Call id param -> 
					case lookupFun env id param of
						Ok _ -> Ok env
						_ -> Bad ("Bad typeing\n")
				_ -> Bad ("Bad typeing\n")
		LExprStmt lexpr ->
			case checkLExpr env lexpr of
				Ok _ -> Ok env
				_ -> Bad ("Bad typeing\n")
		_ -> Bad ("Bad typeing\n")

checkRExpr :: Env -> RExpr -> Err Type
checkRExpr env rexpr =
	case rexpr of
		InfixOp typOp rexpr1 rexpr2 ->
			case typOp of
				ArithOp _ -> 
					case checkRExpr env rexpr1 of
						Ok T_Float -> 
							case checkRExpr env rexpr2 of
								Ok T_Float -> Ok T_Float
								Ok T_Int -> Ok T_Float
								Ok T_Char -> Ok T_Float
								_ -> Bad ("Bad typing\n")
						Ok T_Int -> 
							case checkRExpr env rexpr2 of
								Ok T_Int -> Ok T_Int
								Ok T_Char -> Ok T_Int
								_ -> Bad ("Bad typing\n")
						Ok T_Char -> 
							case checkRExpr env rexpr2 of
								Ok T_Char -> Ok T_Char
								_ -> Bad ("Bad Typing\n")
						_ -> Bad ("Bad typing\n")
				RelOp _ -> 
					case checkRExpr env rexpr1 of
						Ok T_Float -> 
							case checkRExpr env rexpr2 of
								Ok T_Float -> Ok T_Float
								Ok T_Int -> Ok T_Float
								Ok T_Char -> Ok T_Float
								_ -> Bad ("Bad typing\n")
						Ok T_Int -> 
							case checkRExpr env rexpr2 of
								Ok T_Int -> Ok T_Int
								Ok T_Char -> Ok T_Int
								_ -> Bad ("Bad typing\n")
						Ok T_Char -> 
							case checkRExpr env rexpr2 of
								Ok T_Char -> Ok T_Char
								_ -> Bad ("Bad Typing\n")
						Ok Boolean ->
							case checkRExpr env rexpr2 of
								Ok Boolean -> Ok Boolean
								_ -> Bad ("Bad Typing\n")
						_ -> Bad ("Bad typing\n")
				BoolOp _ ->
					case checkRExpr env rexpr1 of
						Ok Boolean -> 
							case checkRExpr env rexpr2 of
								Ok Boolean -> Ok Boolean
								_ -> Bad ("Bad typing\n")
						_ -> Bad ("Bad typing\n")
		UnaryOp _ rexpr ->
			case checkRExpr env rexpr of
				Ok Boolean -> Ok Boolean
				_ -> Bad ("Bad typing\n")
		Ref lexpr -> 
			case checkLExpr env lexpr of
				Ok (Pointer typ) -> Ok (Pointer typ)
				_ -> Bad ("Bad typing\n")
		FCall id param -> lookupFun env id param
		Lexpr lexpr -> checkLExpr env lexpr
		Int _ -> Ok T_Int
		Char _ -> Ok T_Char
		Double _ -> Ok T_Float
		Bool _ -> Ok Boolean
		_ ->  Bad ("Bad typing\n")

lookupFun :: Env -> Ident -> [RExpr] -> Err Type
lookupFun [] id param = Bad ("Function isn't declared\n")
lookupFun env@(scope:scopes) id param = 
	case lookup id (fst scope) of
		Nothing -> lookupFun scopes id param
		Just sig -> checkParam env sig param

checkParam :: Env -> (Type, [(Type, Modality)]) -> [RExpr] -> Err Type
checkParam env ptyp param = checkP env ( map fst ((\(typ, lpar) -> lpar ) ptyp)) param ((\(typ, lpar) -> typ) ptyp)
	where 
		checkP :: Env -> [Type] -> [RExpr] -> Type -> Err Type
		checkP env [] (param:_) typ = Bad ("Error Parameter\n") 
		checkP env (ptyp:_) [] typ = Bad ("Error Parameter\n") 
		checkP env [] [] typ = Ok typ
		checkP env (ptyp:ptyps) (param:params) typ = 
			if (checkRExpr env param == Ok ptyp) then 
				checkP env ptyps params typ
			else 
				Bad ("Error Parameter\n") 

checkLExpr :: Env -> LExpr -> Err Type
checkLExpr env lexpr = 
	case lexpr of
		Deref rexpr -> checkRExpr env rexpr
		PrePostIncDecr _ _ lexpr -> 
			case checkLExpr env lexpr of
				Ok T_Float -> Ok T_Float
				Ok T_Int -> Ok T_Int
				Ok T_Char -> Ok T_Char
				_ -> Bad ("Bad typing\n") 
		BasLExpr blexpr -> checkBLExpr env blexpr
		_ -> Bad ("Bad typing\n") 

checkBLExpr :: Env -> BLExpr -> Err Type
checkBLExpr env blexpr = 
	case blexpr of	
		Id id -> lookupVar env id
		ArrayEl blexpr rexpr ->
			case checkRExpr env rexpr of
				Ok T_Int -> 
					case checkBLExpr env blexpr of
						Ok (ArrDef typ len) -> Ok (ArrDef typ len)
						_ -> Bad ("Bad typing\n")
				_ -> Bad ("Bad Typing\n")

lookupVar :: Env -> Ident -> Err Type
lookupVar [] id = Bad ("Variable not declared\n")
lookupVar (scope:scopes) id = 
	case lookup id (snd scope) of
		Nothing -> lookupVar scopes id
		Just var -> Ok (fst var)
