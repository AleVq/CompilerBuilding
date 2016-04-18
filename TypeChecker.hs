-- copyright FEDERICO BALDO, ALESSANDRO VASQUEZ, ALESSANDRO BURIGANA

module TypeChecker where

import AbsC 
import ErrM

type Fun = (Ident, (Type, [(Type, Modality)]))
type Var = (Ident, Type)

type Env = [([Fun], [Var])]

bEnv = [([((Ident "writeInt"), ((BasTyp T_Void), [(BasTyp T_Int, M_Ref)]))
		 ,((Ident "writeFloat", ((BasTyp T_Void), [(BasTyp T_Float, M_Ref)]))
		 ,((Ident "writeChar", ((BasTyp T_Void), [(BasTyp T_Char, M_Ref)]))
		 ,((Ident "readInt"), ((BasTyp T_Int), []))
		 ,((Ident "readFloat"), ((BasTyp T_Float), []))
		 ,((Ident "readChar"), ((BasTyp T_Char), []))], [])]

typechecker :: Program -> Err ()
typechecker (Prog []) = Ok
typechecker (Prog decls) = 
	do
		env <- checkDsFun bEnv decls
		checkDecls bEnv decls 

addScope :: Env -> Err Env 
addScope env = Ok ( ([],[]) : env )

remScope :: Env -> Err Env
remScope [] = Bad ("erroe\n")
remScope (scope:scopes) = Ok scopes

addVar :: Env -> Ident -> Type -> Err Env
addVar (scope:scopes) id typ = 
	case lookup id (snd scope) of 
		Nothing -> Ok ((fst scope, (id, typ) : (snd scope)) : scopes)
		Just _ -> Bad ("errore\n")

addVars :: Env -> [Ident] -> Type -> Err Env
addVars env [] _ = Ok env
addVars env (id:ids) typ =
	do
		env_ <- addVar env id typ
		addVars env_ ids typ


addFun :: Env -> Ident -> Type -> [Parameter] -> Err Env
addFun env@(scope:scopes) id typ param = 
	case lookup id (fst scope) of
		Nothing ->
			do 
				env2 <- addScope env -- enviroment della funzione 
				{- add parameters -}
				env3 <- foldM (\env (Param mod typ id) -> addVar env id typ) env2 param

				let sig = (typ, map (\(Param mod typ id) -> (typ, mod)) param)

				Ok ((\(scope1:scope2:scopes) -> scope1:((id, sig):fst scope, snd scope):scopes) env3)
		Just _ -> Bad("errore\n")

checkDsFun :: Env -> [Decl] -> Err Env
checkDsFun env [] = Ok env
checkDsFun env (dfun:dsfun) = 
	do
		env_ <- checkDFun env dfun
		checkDsFun env_ dfuns

checkDFun :: Env -> Decl -> Err Env
checkDFun env dfun =
	case dfun of 
		Dfun typ id param _ -> addFun env id typ param

checkDecls :: Env -> [Decl] -> Err Env
checkDecls env [] = Ok env
checkDecls env (decl:decls) =
	case decl of
		Dvar typ (vdecl:vdecls) -> 
			case checkRExp env (\(VarDecl id exp) -> exp) of 
				Ok _ ->
					do 
						env_ <- addVar env (\(VarDecl id exp) -> id) typ
						checkDecls env_ decls
				_ -> Bad ("Bad Typing son of a bitch\n")

		Dfun _ _ _ stmts_decls ->
				do 
					checkStmtsDels env stmts_decls typ 
					env_ <- remScope env
					Ok env_

checkStmtsDels :: Env -> [Stmt_Decl] -> Type -> Err Env
checkStmtsDels env [] _ _ -> Ok env
checkStmtsDels env (st_de:sts_des) typ =
	do 
		env_ <- checkStmtDel env st_de typ
		checkStmtsDels env_ sts_des typ

checkStmtDel :: Env -> Stmt_Decl -> Type -> Err Env
checkStmtDel env st_de typ =
	case (\(_ st_de) -> st_de) of
		Dvar _ _ -> checkDecls env st_de 
		Dfun _ _ _ _ -> checkDecls env st_de
		RetExpVoid -> case typ of
						T_Void -> Ok env
						_ -> Bad ("bad typing\n")
		RetExp exp -> 
				case checkLExpr env lexpr of
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
		Assgn lexpr Assignment_op rexpr -> 
				case checkLExpr env lexpr of
					Ok T_Float ->
						case checkRExp env rexpr of
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
		PrePostIncDecr _ _ lexpr -> 
				case checkLExpr env lexpr of
					Ok T_Float -> Ok env
					Ok T_Int -> Ok env
					_ -> Bad ("Bad typing\n")
		IfNoElse rexpr sts_des -> 
				case checkRExpr env rexpr of
					Ok Boolean -> checkStmtsDels sts_des
					_ -> Bad ("Bad typing\n")
		IfElse rexpr st1_de1 st2_de2 ->
				case checkRExpr env rexpr of
					Ok Boolean -> checkStmtsDels env (st1_de1++st2_de2)
					_ -> Bad ("Bad Typing\n")
		While rexpr loop_ops -> 
				case checkRExpr env rexpr of
					Ok Boolean -> checkLoopOps env loop_ops typ
					_ -> Bad ("Bad typing\n")
		DoWhile loop_ops rexpr ->
				case checkRExpr env rexpr of
					Ok Boolean -> checkLoopOps env loop_ops typing
					_ -> Bad ("Bad typing\n")
		For st1_de1 rexpr st2_de2 loop_ops ->
				case checkStmtDel env st1_de1 of
					Ok env -> 
						case checkRExpr env rexpr of
							Ok Boolean -> 
								case checkStmtDecl env st2_de2 of
									Ok env -> checkLoopOps env loop_ops typ
									_ -> Bad ("Bad typeing\n")
							_ -> Bad ("Bad typeing\n")
					_ -> Bad ("Bad typeing\n")


checkLoopOps :: Env -> [LoopOp] -> Err Env
checkLoopOps env [] _ = Ok env
checkLoopOps env (l_op:l_ops) typ= 
	do 
		env_ <- checkLoopOp env l_op typ
		checkLoopOps env l_ops typ

checkLoopOp :: Env -> LoopOp -> Err Env
checkLoopOp env l_op = 
	case l_op of
		Break -> Ok env
		Continue -> Ok env
		st_de -> checkStmtsDels env st_de typing

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
								Ok T_Char -> T_Char
								_ -> Bad ("Bad Typing\n")
						_ -> Bad ("Bad typing\n")
				RelOp  -> 
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
								Ok T_Char -> T_Char
								_ -> Bad ("Bad Typing\n")
						Ok Boolean ->
							case checkRExpr env rexpr2 of
								Ok Boolean -> Boolean
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
			case checkLexpr env lexpr of
				Ok Pointer typ -> Ok (Pointer typ)
				_ -> Bad ("Bad typing\n")
		Const _ typ -> Ok typ
		RFCall id param ->
			case lookupFun env id param of
				Ok typ -> Ok typ
				_ -> Bad ("Bad typing\n")
		Lexpr lexpr -> checkLExpr env lexpr

lookupFun :: Env -> Ident -> [RExpr] -> Err Type
lookupFun [] id param = Bad ("Function isn't declared\n")
lookupFun (scope:scopes) id param = 
	case lookup id (fst scope) of
		Nothing -> lookupFun scopes id param
		Just sig -> 
			do 
				case checkParam (snd.snd$sig) param of
					Ok _ -> Ok typ
					_ -> Bad ("Bad typing\n")
						where 
							typ = fst . snd $ sig

checkParam :: [Type] -> [RExpr] -> Err ()
checkParam ptyp param = checkP (map (\(typ,_) -> typ) ptyp ) param
	where 
		checkP [] (param:_) = Bad ("Error Parameter\n") 
		checkP (ptyp:_) [] = Bad ("Error Parameter\n") 
		checkP [] [] = Ok 
		checkP (ptyp:ptyps) (param:params) = 
			if (checkRExpr param == Ok ptyp) then 
				checkP ptyps params
			else 
				Bad ("Error Parameter\n") 

checkLExpr :: Env -> LExpr -> Err Type
checkLexpr env lexpr = 
	case lexpr of
		Deref rexpr -> checkRExpr env rexpr
		Id id -> lookupVar env id
		ArrayEl lexpr rexpr ->
			case checkRExpr env rexpr of
				Ok T_Int -> 
					case checkLExpr env lexpr of
						Ok ArrDef typ len -> Ok (ArrDef typ len)
						_ -> Bad ("Bad typing\n")
				_ -> Bad ("Bad Typing\n")
		LFCall id param ->
			case lookupFun env id param of
				Ok typ -> Ok typ
				_ -> Bad ("Bad typing\n")

lookupVar :: Env -> Ident -> Err Type
lookupVar [] id = Bad ("Variable not declared\n")
lookupVar (scope:scopes) id = 
	case lookup id (snd scope) of
		Nothing -> lookupVar scopes id
		Just var -> Ok (fst var)