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

(*Big Step Eval :*)	
type value = N of int
	| B of bool
	| Clsr of ident*term*env
	| RecClsr of ident*ident*term*env
	and env = (ident*value) list;;  (*and necessário porque declaração*)

(*funçãozinha auxiliar que será usada em BS-LET e BS-LETREC*)
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


	
	


	
