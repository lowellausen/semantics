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
	

	
(*Big Step:*)	
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
		(eval (insertEnv x this_term environment) e2)
	
	(*BS-LETREC*)
	|TmLet_rec(f, (typeI, typeO), (x, typeX, e1), e2) ->
		let this_term = bs_eval environment (TmFn(x, typeX, e1)) in
		(
	


	
	


	