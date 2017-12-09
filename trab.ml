(*trabalhinho de semântica 2017/2*)
(*Não creio que se faz comentário assim*)

type op = Sum|Sub|Mult|Great|GreatEq|Eq|Diff|LessEq|Less;;

type typ = TInt | TBool | TFn of typ * typ;;

type ident = string;;

type term = N of int 
	| B of bool
	| EopE of term * op * term
	| If of term * term * term
	| X of ident
	| EE of term * term
	| Fn of ident * typ * term
	| Lett of ident * typ * term * term
	| Let_rec of ident * (typ * typ) * (ident * typ * term) * term;;	