(*trabalhinho de semântica 2017/2*)
(*Não creio que se faz comentário assim*)

(*Sintaxe Abstrata:*)
type op = Sum
	|Sub
	|Mult
	|Great
	|GreatEq
	|Eq
	|Diff
	|LessEq
	|Less;;

type typ = TInt 
	| TBool 
	| TFn of typ * typ;;

type ident = string;;

type term = TmN of int 
	| TmB of bool
	| TmEopE of term * op * term
	| TmIf of term * term * term
	| TmX of ident
	| TmEE of term * term
	| TmFn of ident * typ * term
	| TmLet of ident * typ * term * term
	| TmLet_rec of ident * (typ * typ) * (ident * typ * term) * term;;
	

(*exceptions*)
exception Identifier_Not_Found
exception Now_its_Exhaustive
exception Type_Error
exception Empty_Stack

(*Big Step Eval :*)	
type value = N of int
	| B of bool
	| Clsr of ident*term*env
	| RecClsr of ident*ident*term*env
	and env = (ident*value) list;;  (*and necessário porque declaração*)

(*funçãozinha auxiliar que será usada em BS-LET e BS-LETREC BS-APP e outra para o sistemas de tipos*)
let rec insertEnv identifier ident_value envir : env = match envir with
	| [] -> [(identifier, ident_value)]
	| hd::tl -> List.append [(identifier, ident_value)] envir 
	

let rec bs_eval environment e : value = match e with
	
	(*BS-NUM*)
	TmN(num) -> N(num)
	
	(*BS-BOOL*)
	|TmB(boool) -> B(boool)
	
	(*BS-ID*)
	(*TESTAR!!!!!*)
	|TmX(x) -> 
		let rec findValue identifier envir : value = match envir with 
			[] -> raise Identifier_Not_Found
			| (this_ident, this_val)::term_rest ->
				if(this_ident = identifier)
				then this_val
				else findValue identifier term_rest in
		(findValue x environment)
	
	(*BS-IFTR*)
	|TmIf(e1, e2, e3) when ((bs_eval environment e1) = B(true)) -> bs_eval environment e2
	
	(*BS-IFFLS*)
	|TmIf(e1, e2, e3) when ((bs_eval environment e1) = B(false)) -> bs_eval environment e3
	
	(*BS-FN*)
	|TmFn(x, this_type, this_term) -> Clsr(x, this_term, environment)
	
	(*BS-LET*)
	|TmLet(x, this_type, e1, e2) ->
		let this_term = bs_eval environment e1 in
		(bs_eval (insertEnv x this_term environment) e2)
	
	(*BS-LETREC*)
	|TmLet_rec(f, (typeI, typeO), (x, typeX, e1), e2) ->
		let this_term = bs_eval environment (TmFn(x, typeX, e1)) in
		(match this_term with
			| Clsr(x_term, func_term, env_term) -> bs_eval (insertEnv f (RecClsr(f, x_term, func_term, environment)) env_term) e2 
			| _ -> raise Now_its_Exhaustive (*killing warnings*)
		)

	(*BS-APP*)
	(*
	| TmEE(e1, e2) ->
		let term_e1 = bs_eval environment e1 in
		let term_e2 = bs_eval environment e2 in
		(match term_e1, term_e2 with
			Clsr(x, e1_term, e1_env), val_e2 -> bs_eval (insertEnv x val_e2 e1_env) e1_term
			| _ -> raise Now_its_Exhaustive (*killing warnings*)
		)
	*)

	(*BS_APP +++ BS-APPREC  juntas porque usam o mesmo pattern matching*)
	| TmEE(e1, e2) ->
		let term_e1 = bs_eval environment e1 in
		let term_e2 = bs_eval environment e2 in
		(match term_e1, term_e2 with
			Clsr(x, e1_term, e1_env), val_e2 -> bs_eval (insertEnv x val_e2 e1_env) e1_term
			|RecClsr(f, x, e1_term, e1_env), val_e2 -> bs_eval (insertEnv f (RecClsr(f, x, e1_term, e1_env)) (insertEnv x val_e2 e1_env)) e1_term
			| _ -> raise Now_its_Exhaustive (*killing warnings*)
		)

	(*BS-OP    não está no resumo-l1 mas parece necessário*)
	|TmEopE(e1, op, e2) ->
		let term_e1 = bs_eval environment e1 in
		let term_e2 = bs_eval environment e2 in
		(match term_e1, op, term_e2 with
			N(v1), Sum, N(v2) -> N(v1 + v2)
			|N(v1), Sub, N(v2) -> N(v1 - v2)
			|N(v1), Mult, N(v2) -> N(v1 * v2)
			|N(v1), Great, N(v2) -> B(v1 > v2)
			|N(v1), GreatEq, N(v2) -> B(v1 >= v2)
			|N(v1), Eq, N(v2) -> B(v1 = v2)
			|N(v1), Diff, N(v2) -> B(v1 <> v2)
			|N(v1), LessEq, N(v2) -> B(v1 <= v2)
			|N(v1), Less, N(v2) -> B(v1 < v2)
			
			| _ -> raise Now_its_Exhaustive (*killing warnings*)
		)
		
	| _ -> raise Now_its_Exhaustive (*killing warnings*);;


(*type system*)
type type_env = (ident * typ) list;;

(*aux para tipos que necessitam atualizar o env*)
let rec insertTypeEnv identifier ident_type envir : type_env = match envir with
	| [] -> [(identifier, ident_type)]
	| hd::tl -> List.append [(identifier, ident_type)] envir

let rec type_system environment e : typ = match e with
	
	(*T-INT*)
	TmN(n) -> TInt
	
	(*T-BOOL*)
	| TmB(b) -> TBool
	
	(*T-OP todos*)
	|TmEopE(e1, op, e2) ->
		let type_e1 = type_system environment e1 in
		let type_e2 = type_system environment e2 in
		(match type_e1, op, type_e2 with
			TInt, Sum, TInt -> TInt
			|TInt, Sub, TInt -> TInt
			|TInt, Mult, TInt -> TInt
			|TInt, Great, TInt -> TBool
			|TInt, GreatEq, TInt -> TBool
			|TInt, Eq, TInt -> TBool
			|TInt, Diff, TInt -> TBool
			|TInt, LessEq, TInt -> TBool
			|TInt, Less, TInt -> TBool
			
			| _ -> raise Now_its_Exhaustive (*killing warnings*)
		)
	
	(*T-IF*)
	|TmIf(e1, e2, e3) ->
		let type_e1 = type_system environment e1 in
		let type_e2 = type_system environment e2 in
		let type_e3 = type_system environment e3 in
		(match type_e1, type_e2, type_e3 with
			TBool, TInt, TInt -> TInt
			|TBool, TBool, TBool -> TBool
			|TBool, TFn(typeI,typeO), TFn(typeI2,typeO2) when(typeI = typeI2 && typeO = typeO2) -> TFn(typeI,typeO)
	
			| _ -> raise Now_its_Exhaustive (*killing warnings*)
		)

	(*T-VAR  testar too*)
	|TmX(x) -> 
		let rec findType identifier envir : typ = match envir with 
			[] -> raise Identifier_Not_Found
			| (this_ident, this_type)::term_rest ->
				if(this_ident = identifier)
				then this_type
				else findType identifier term_rest in
		(findType x environment)
		
	(*T_FUN*)
	|TmFn(x, x_type, f_term) -> TFn(x_type, (type_system (insertTypeEnv x x_type environment) f_term))
	
	(*T-APP*)
	|TmEE(e1, e2) ->
		let type_e1 = type_system environment e1 in
		let type_e2 = type_system environment e2 in
		(match type_e1, type_e2 with
			TFn(e1_typeI, e1_typeO), e2_type when(e1_typeI = e2_type) -> e1_typeO
			| _ -> raise Now_its_Exhaustive (*killing warnings*)
		)
		
	(*T-LET*)
	|TmLet(x, type_x, e1, e2) when(type_x = type_system environment e1) -> type_system environment e2
		
	(*T-LETREC*)
	|TmLet_rec(f, (typeI, typeO), (x, type_x, e1), e2) -> 
		let env_with_x = insertTypeEnv x type_x environment in
		let f_type = TFn(typeI, typeO) in
		(*let env_with_f = insertTypeEnv f TFn(typeI, typeO) env_with_x in*)
		let env_with_f = insertTypeEnv f f_type env_with_x in
		let type_e1 = type_system env_with_f e1 in
		let type_e2 = type_system (insertTypeEnv f f_type environment) e2 in
		(if type_e1 = typeO && typeI = type_x
		then type_e2
		else raise Type_Error
		)
		
	| _ -> raise Now_its_Exhaustive (*killing warnings*);;
	
(*SSM2 compilação*)
type instruction = INT of int |BOOL of bool
	|POP | COPY
	|ADD | INV
	|EQ | GT
	|AND | NOT
	|JUMP of int | JMPIFTRUE of int
	|VAR of ident
	| FUN of ident * code
	| RFUN of ident * ident * code
	|APPLY
and code = instruction list ;; (*de novo, and porque as definições são dependentes*)

type storable_value = SvINT of int
	|SvBOOL of bool
	|SvCLOS of ssm2_env * ident * code
	|SvRCLOS of ssm2_env * ident * ident * code
and stack = storable_value list
and ssm2_env = (ident * storable_value) list
and dump = (code * stack * ssm2_env) list;;

type state = State of code * stack * ssm2_env * dump;;

(*semântica ssm2*)

(*função aux para dividir a lista code. RERTIRADA DO STACK OVERFLOW:
https://stackoverflow.com/questions/31616117/splitting-a-list-using-an-index
*)

let rec split_at1 n l =
	if n = 0 then ([], l) else
	match l with
	| [] -> ([], [])    (*or raise an exception, as you wish*)
	| h :: t -> let (l1, l2) = split_at1 (n-1) t in (h :: l1, l2);;

let rec ssm2_eval cod stck env dp : state = match cod with

	(*as regras não têm nomes :( *)
	(* regra do int*)
	INT(n)::tl -> ssm2_eval tl (List.append [SvINT(n)] stck) env dp
	
	(*regra do bool*)
	|BOOL(b)::tl -> ssm2_eval tl (List.append [SvBOOL(b)] stck) env dp
	
	(*regra do pop*)
	|POP::tl -> (match stck with
					[] -> raise Empty_Stack
					|hd::tls -> ssm2_eval tl tls env dp
				)
				
	(*regra do copy*)
	|COPY::tl -> (match stck with
					[] -> raise Empty_Stack
					|hd::tls -> ssm2_eval tl (List.append [hd] stck) env dp
				)
				
	(*regra do add*)
	|ADD::tl -> (match stck with
					[] -> raise Empty_Stack
					|SvINT(n1)::tls -> (match tls with
											[] -> raise Empty_Stack
											|SvINT(n2)::tltls -> ssm2_eval tl (List.append [SvINT(n1 + n2)] tltls) env dp
										)
				)
				
	
	(*regra do inv*)
	|INV::tl -> (match stck with
					[] -> raise Empty_Stack
					|SvINT(n)::tls -> ssm2_eval tl (List.append [SvINT(-1 * n)] tls) env dp
				)
				
	(*regra do eq*)
	|EQ::tl -> (match stck with
					[] -> raise Empty_Stack
					|SvINT(n1)::tls -> (match tls with
											[] -> raise Empty_Stack
											|SvINT(n2)::tltls -> ssm2_eval tl (List.append [SvBOOL(n1 = n2)] tltls) env dp
										)
				)

	(*regra do gt*)
	|GT::tl -> (match stck with
					[] -> raise Empty_Stack
					|SvINT(n1)::tls -> (match tls with
											[] -> raise Empty_Stack
											|SvINT(n2)::tltls -> ssm2_eval tl (List.append [SvBOOL(n1 > n2)] tltls) env dp
										)

				)
				
	(*regra do and*)
	|AND::tl -> (match stck with
					[] -> raise Empty_Stack
					|SvBOOL(b1)::tls -> (match tls with
											[] -> raise Empty_Stack
											|SvBOOL(b2)::tltls -> ssm2_eval tl (List.append [SvBOOL(b1 && b2)] tltls) env dp
										)
				)
				
	(*regra do not*)
	|NOT::tl -> (match stck with
					[] -> raise Empty_Stack
					|SvBOOL(b)::tls -> ssm2_eval tl (List.append [SvBOOL(not b)] tls) env dp
				)
				
	(*regra do jump*)
	|JUMP(n)::tl -> let (cod1, cod2) = split_at1 n cod in (ssm2_eval cod2 stck env dp)
	
	(*regra do jmpiftrue*)
	|JMPIFTRUE(n)::tl -> let (cod1, cod2) = split_at1 n cod in
						(match stck with
							[] -> raise Empty_Stack
							|SvBOOL(b)::tls -> (if z1 then (ssm2_eval cod2 tls env dp) else (ssm2_eval tl tls env dp))
						)
	
	(*regra do var*)
	|VAR(x)::tl -> 
		let rec findSValue identifier envir : storable_value = match envir with 
			[] -> raise Identifier_Not_Found
			| (this_ident, this_sval)::env_rest ->
				if(this_ident = identifier)
				then this_sval
				else findSValue identifier env_rest in
		(ssm2_eval tl (List.append [findValue x environment] stck) env dp)
	
	(*regra do fun*)
	|FUN(x, cod_f)::tl -> ssm2_eval tl (List.append [SvCLOS(env, x, cod_f)] stck) env dp
	
	(*regra do apply*)
	|APPLY::tl ->