(*
=====*=====*=====*=====*=====*=====

	UNIVERSIDADE FEDERAL DO RIO GRANDE DO SUL
	INSTITUTO DE INFORMÁTICA
	DEPARTAMENTO DE INFORMÁTICA TEÓRICA
	INF05516 - Semântica Formal - Turma U
	Prof. Dr. Alvaro Moreira

	Trabalho Final - 2017/1
	06 de Julho de 2017

	Nome: Lucas Flores		Matrícula: 242317
	Nome: Raphael Piegas	Matrícula: 217438
	Nome: Taiane Peixoto	Matrícula: 228369

=====*=====*=====*=====*=====*=====

	DESCRIÇÃO:
		O trabalho consiste da implementação de um interpretador composto de um avaliador de
	expressões e de uma inferência de tipos para a linguagem L1 cuja sintaxe abstrata é dada
	abaixo. Tanto o avaliador de expressões como a inferência de tipos devem seguir estritamente
	a semântica operacional e o sistema de tipos definidos para L1. O avaliador de expressões
	deve ser implementado seguindo as regras da semântica operacional dadas no estilo big step.

	e ∈ Terms
	e ::= n
		| b
		| e1 op e2
		| if e1 then e2 else e3
		| x
		| e1 e2
		| fn x:T ⇒ e
		| let x:T = e1 in e2
		| let rec f:T1 → T2 = (fn y:T1 ⇒ e1) in e2

	onde
		n ∈ conjunto de numerais inteiros
		b ∈ {true, false}
		x ∈ Ident
		op ∈ {+, −, ∗, div, ==, and, or, not}

	PONTOS EXTRAS:
		A notá máxima para o trabalho descrito acima é 10. Os grupos que implementarem também
	(i) um interpretador para a linguagem da máquina abstrata SSM2 e (ii) a compilação de L1
	para a linguagem da máquina abstrata SSM2 poderão obter até 12 pontos.

*)

type variable = string;;

type operator =
	Sub
	| Or
	| Sum
	| Div
	| And
	| Mult
	| Less
	| Equal
	| Greater
	| NotEqual
	| LessOrEqual
	| GreaterOrEqual
;;

type tipo =
	TyInt
	| TyBool
	| TyFn of tipo * tipo
;;

type expr =
	Num of int
	| Bool of bool
	| Bop of expr * operator * expr
	| If of expr * expr * expr
	| Var of variable
	| App of expr * expr
	| Func of variable * tipo * expr
	| Let of variable * tipo * expr * expr
	| LetRec of variable * (tipo * tipo) * (variable * tipo * expr) * expr
	| Not of expr
;;

type value =
	Vnum of int
	| Vbool of bool
	| Vclos of variable * expr * env
	| Vrclos of variable * variable * expr * env
and
	env = (variable * value) list
and
	tenv = (variable * tipo) list
;;


(*
=====*=====*=====*=====*=====*=====
	CONTROLE DO AMBIENTE
=====*=====*=====*=====*=====*=====
*)

(* ==*== Atualizar o ambiente ==*== *)

	let updateEnv variable v environment : env = match environment with
		|[] -> [(variable, v)]
		| hd::tl -> List.append [(variable, v)] environment

(* ==*== Busca no ambiente ==*== *)

	let rec searchEnv variable environment : value = match environment with
		| [] -> raise Not_found
		| (k, v)::tl ->
			if (k = variable)
			then v
			else searchEnv variable tl

(* ==*== Atualizar o ambiente de tipos ==*== *)

	let updateTEnv variable tipo environment : tenv = match environment with
		|[] -> [(variable, tipo)]
		| hd::tl -> List.append [(variable, tipo)] environment

(* ==*== Busca no ambiente de tipos ==*== *)

	let rec searchTEnv variable environment : tipo = match environment with
		| [] -> raise Not_found
		| (k, v)::tl ->
			if (k = variable)
			then v
			else searchTEnv variable tl

(* ==*== Ambiente vazio (usamos nos testes) ==*== *)

	let t_emptyEnv : tenv = []

(* ==*== Ambiente vazio (usamos nos testes) ==*== *)

	let emptyEnv : env = []

(*
=====*=====*=====*=====*=====*=====
	AVALIAÇÃO - BIG STEP
=====*=====*=====*=====*=====*=====
*)

	let rec eval environment e : value = match e with

		(* ==*== Valores ==*== *)
		Num(n) -> Vnum(n)
		| Bool(b) -> Vbool(b)

		(* ==*== Operações binárias ==*== *)
		| Bop(e1, op, e2) -> 
			let exp1 = eval environment e1 in
			let exp2 = eval environment e2 in
			(match exp1, op, exp2 with

				(* ==*== retorna tipo inteiro ==*== *)
				Vnum(exp1), Sum, Vnum(exp2) -> Vnum(exp1 + exp2)
				|Vnum(exp1), Sub, Vnum(exp2) -> Vnum(exp1 - exp2)
				|Vnum(exp1), Div, Vnum(exp2) -> Vnum(exp1 / exp2)
				|Vnum(exp1), Mult, Vnum(exp2) -> Vnum(exp1 * exp2)

				(* ==*== retorna tipo booleano ==*== *)
				|Vnum(exp1), Equal, Vnum(exp2) -> Vbool(exp1 = exp2)
				|Vbool(exp1), Equal, Vbool(exp2) -> Vbool(exp1 = exp2)
				|Vnum(exp1), NotEqual, Vnum(exp2) -> Vbool(exp1 <> exp2)
				|Vbool(exp1), NotEqual, Vbool(exp2) -> Vbool(exp1 <> exp2)
				|Vnum(exp1), Less, Vnum(exp2) -> Vbool(exp1 < exp2)
				|Vnum(exp1), LessOrEqual, Vnum(exp2) -> Vbool(exp1 <= exp2)
				|Vnum(exp1), Greater, Vnum(exp2) -> Vbool(exp1 > exp2)
				|Vnum(exp1), GreaterOrEqual, Vnum(exp2) -> Vbool(exp1 >= exp2)
				|Vbool(exp1), And, Vbool(exp2) -> Vbool(exp1 && exp2)
				|Vbool(exp1), Or, Vbool(exp2) -> Vbool(exp1 || exp2)

				(* ==*== caso de falha ==*== *)
				| _ -> failwith "bop_not_found"
			)

		(* ==*== if then else ==*== *)
		| If(e1, e2, e3) when ((eval environment e1) = Vbool(true)) -> eval environment e2
		| If(e1, e2, e3) when ((eval environment e1) = Vbool(false)) -> eval environment e3

		(* ==*== Variavel ==*== *)
		| Var(variable) -> searchEnv variable environment

		(* ==*== Função ==*== *)
		| Func(variable, t, e) -> Vclos(variable, e, environment)

		(* ==*== Aplicação ==*== *)
		| App(e1, e2) -> 
			let exp3 = eval environment e1 in
			let exp4 = eval environment e2 in
			(match exp3, exp4 with
				Vclos(var, e, envi), v -> eval (updateEnv var v envi) e
				| Vrclos(f, x, e, envi), v -> eval (updateEnv f (Vrclos(f, x, e, envi)) (updateEnv x v envi)) e

				(* ==*== caso de falha ==*== *)
				| _ -> failwith "app_not_found"
			)

		(* ==*== Let ==*== *)
		| Let(var, t, e1, e2) ->
			let exp5 = eval environment e1 in
			eval (updateEnv var exp5 environment) e2

		(* ==*== Let Rec ==*== *)
		| LetRec(f, (t1, t2), (var, t3, e1), e2) ->
			let exp6 = eval environment (Func(var, t3, e1)) in
			(match exp6 with
				| Vclos(x, e, env) -> eval (updateEnv f (Vrclos(f, x, e, environment)) env) e2

				(* ==*== caso de falha ==*== *)
				| _ -> failwith "letrec_not_found"
			)

		(* ==*== Not ==*== *)
		| Not(e) when ((eval environment e) = Vbool(true)) -> Vbool(false)
		| Not(e) when ((eval environment e) = Vbool(false)) -> Vbool(true)

		(* ==*== caso de falha ==*== *)
		| _ -> failwith "eval_not_found"
	;;

	(*
	=====*=====*=====*=====*=====*=====
		INFERÊNCIA DE TIPOS
	=====*=====*=====*=====*=====*=====
	*)


	let rec typecheck environment e : tipo = 
		match e with
		(* VALORES *)
		  Num(e) -> TyInt
		| Bool(e) -> TyBool

		(* OPERAÇÕES BINÁRIAS *)
		| Bop(e1, op, e2) ->
			let exp1 = typecheck environment e1 in
			let exp2 = typecheck environment e2 in
			(match exp1, op, exp2 with

				(* Retorna Tipo Int *)
				  TyInt, Sum, TyInt -> TyInt
				| TyInt, Sub, TyInt -> TyInt
				| TyInt, Mult, TyInt -> TyInt
				| TyInt, Div, TyInt -> TyInt
				(* Retorna Tipo Bool *)
				| TyInt, Equal, TyInt -> TyBool
				| TyBool, Equal, TyBool -> TyBool
				| TyBool, NotEqual, TyBool -> TyBool
				| TyInt, NotEqual, TyInt -> TyBool
				| TyInt, GreaterOrEqual, TyInt -> TyBool
				| TyBool, And, TyBool -> TyBool
				| TyBool, Or, TyBool -> TyBool
				| TyInt, Less, TyInt -> TyBool
				| TyInt, LessOrEqual, TyInt -> TyBool
				| TyInt, Greater, TyInt -> TyBool
				| _ -> failwith "ERROR: 'BOP' NOT FOUND"
			)


		(* NOT *)
		| Not(e) -> 
			let exp1 = typecheck environment e in
			(match exp1 with 
				  TyBool -> TyBool
				| _ ->failwith "ERROR: 'NOT' NOT FOUND"
			)


		(* CONDICIONAL *)
		| If(e1, e2, e3) ->
			if (typecheck environment e1) = TyBool
			then 
				let t1 = typecheck environment e2 in
				let t2 = typecheck environment e3 in
				(	if t1 = t2
					then t1
					else failwith "ERROR: DIFFRENT TYPES"
				) 
			else failwith "ERROR: 'IF' NOT FOUND"


		(* VARIÁVEL *)
		| Var(variable) -> searchTEnv variable environment


		(* APLICAÇÃO *)
		| App(e1, e2) ->
			let expapp1 = typecheck environment e1 in
			let expapp2 = typecheck environment e2 in
			(match expapp1 with
				TyFn(t1, t2) -> (if t2 = expapp2
								then expapp2
								else failwith "ERROR: 'APP' NOT FOUND")
				| _ -> failwith "ERROR: 'APP' NOT FOUND"

			)
						
		(* FUNÇÃO *)
		| Func(variable, t, e) -> TyFn(t, (typecheck (updateTEnv variable t environment) e))
		
		(* LET *)
		| Let(variable, t, e1, e2) ->
			let v = typecheck environment e1 in (
				if v = t
				then typecheck (updateTEnv variable t environment) e2
				else failwith "ERROR: 'APP' NOT FOUND")

		(* LET REC *)
		| LetRec(f, (t1, t2), (var, t3, e1), e2) ->
			let t5 = TyFn(t1, t2) in
			let update1 = updateTEnv var t3 environment in
			let update2 = updateTEnv f t5 update1 in
			let t4 = typecheck update2 e1 in (
				if t4 = t2 && t1 = t3
				then typecheck (updateTEnv f t5 environment) e2
				else failwith "ERROR: 'LET REC' NOT FOUND"
			)

			(* *)
		
		
		;;


(*
=====*=====*=====*=====*=====*=====
	TESTES
=====*=====*=====*=====*=====*=====
*)


	(* ==*== Ambiente vazio ==*== *)
	let environment = emptyEnv;;
	
	(* ==*== Valores basicos ==*== *)
	let numTest = Vnum (5);;
	let boolTest = Vbool (true);;

	(* ==*== Estrutura do ambiente ==*== *)
	let envir = updateEnv "numTest" numTest environment;;
	searchEnv "numTest" envir;;
	let envir' = updateEnv "ten" (Vnum(10)) envir;;
	let envir''= updateEnv "numTest" (Vnum(6)) envir';;
	searchEnv "numTest" envir;;


	(* ==*== EXPRESSÕES ==*== *)

	(* ==*== Not ==*== *)
	let notOK = Not(Bool(true));;
	let notFail = Not(Num(1));;


	(* ==*== Bop ==*== *)
	(* 	Sub 	*)
	let bopSubOK = Bop(Num(10), Sub, Num(5));;
	let bopSubFail = Bop(Bool(false), Sub, Num(5));;

	(*	| Or 	*)
	let bopOrOK = Bop(Bool(false), Or, Bool(true));;
	let bopOrFail = Bop(Bool(false), Or, Num(5));;

	(*	| Sum 	*)
	let bopSumOK = Bop(Num(10), Sum, Num(5));;
	let bopSumFail = Bop(Bool(false), Sum, Num(5));;

	(*	| Div 	*)
	let bopDivOK = Bop(Num(10), Div, Num(5));;
	let bopDivFail = Bop(Bool(false), Div, Num(5));;

	(*	| And 	*)
	let bopAndOK = Bop(Bool(false), And, Bool(true));;
	let bopAndFail = Bop(Bool(false), And, Num(5));;

	(*	| Mult 	*)
	let bopMultOK = Bop(Num(10), Mult, Num(5));;
	let bopMultFail = Bop(Bool(false), Mult, Num(5));;

	(*	| Less 	*)
	let bopLessOK = Bop(Num(10), Less, Num(5));;
	let bopLessFail = Bop(Bool(false), Less, Num(5));;

	(*	| Equal 	*)
	let bopEqNumOK = Bop(Num(10), Equal, Num(5));;
	let bopEqNumFail = Bop(Bool(false), Equal, Num(5));;

	let bopEqBoolOK = Bop(Bool(false), Equal, Bool(true));;
	let bopEqBoolFail = Bop(Bool(false), Equal, Num(5));;

	(*	| Greater 	*)
	let bopGreaterOK = Bop(Num(10), Greater, Num(5));;
	let bopGreaterFail = Bop(Bool(false), Greater, Num(5));;

	(*	| NotEqual 	*)
	let bopNotEqNumOK = Bop(Num(10), NotEqual, Num(5));;
	let bopNotEqNumFail = Bop(Bool(false), NotEqual, Num(5));;

	let bopNotEqBoolOK = Bop(Bool(false), NotEqual, Bool(true));;
	let bopNotEqBoolFail = Bop(Bool(false), NotEqual, Num(5));;

	(*	| LessOrEqual 	*)
	let bopLessOrEqualOK = Bop(Num(10), LessOrEqual, Num(5));;
	let bopLessOrEqualFail = Bop(Bool(false), LessOrEqual, Num(5));;

	(*	| GreaterOrEqual 	*)
	let bopGreaterOrEqualOK = Bop(Num(10), GreaterOrEqual, Num(5));;
	let bopGreaterOrEqualFail = Bop(Bool(false), GreaterOrEqual, Num(5));;


	(* ==*== IF ==*== *)
	let ifTrue = If(Bop(Num(99), NotEqual, Num(25)), Bool(true), Bool(false));;
	let ifFalse = If(Bop(Num(99), NotEqual, Num(25)), Bool(true), Bool(false));;
	let ifFail = If(Bop(Num(99), Sub, Num(25)), Num(44), Num(72));;


	(* ==*== FUNCTION ==*== *)
	let funcOk = Func("x", TyInt, Bop(Var("x"), Sub, Num(1)));;


	(* ==*== APLICAÇÃO ==*== *)
	let appVar = Var("x");;
	let appOK = App(Func("x", TyInt, Bop(appVar, Sub, Num(4))), Num(5));;


	(* ==*== LET ==*== *)
	let letOK01 = Let("x", TyInt, Num(2), Bop(Var("x"), Sub, Num(2)));;
	let letOK02 = Let("x", TyInt, Num(2), Let("y", TyInt, Num(2), Bop(Var("x"), Mult, Var("y"))));;
	let letOK03 = Let("x", TyInt, Num(111), If(Bop(Var("x"), Equal, Num(111)), Bool(true), Bool(false)));;


	(* ==*== LET REC ==*== *)
		(* ==*== EX. FATORIAL - FAT(10) ==*== *)
	let letRecOK01 = LetRec("fat", (TyInt, TyInt), ("x", TyInt,
							If(Bop(Var("x"), Equal, Num(0)),
								Num(1),
								Bop(Var("x"), Mult, App(Var("fat"), Bop(Var("x"), Sub, Num(1))))
							)),
							App(Var("fat"), Num(10))
						);;

		(* ==*== EX. FIBONACCI - FIB(10)  ==*== *)
	let letRecOK02 = LetRec("fib", (TyInt, TyInt), ("x", TyInt,
							If(Bop(Var("x"), Less, Num(2)),
								Var("x"),
								Bop(App(Var("fib"), Bop(Var("x"), Sub, Num(1))), Sum, App(Var("fib"), Bop(Var("x"), Sub, Num(2))))
							)),
							App(Var("fib"), Num(10))
						);;


	let print_value s v : unit =
		(match v with 
			| Vnum(n) -> Printf.printf "A avaliação de %s resultou em Vnum %d\n\n" s n
			| Vbool(b) -> Printf.printf "A avaliação de %s resultou em Vbool %B\n\n" s b
			| Vclos(var, exp, env) -> Printf.printf "A avaliação de %s resultou em uma Vclos\n\n" s
			| Vrclos(f, var, exp, env) ->  Printf.printf "A avaliação de %s resultou em uma Vrclos\n\n" s
		)

	let rec print_tipo_fn t : string =
		(match t with 
			| TyInt-> "int" 
			| TyBool -> "bool" 
			| TyFn(t1, t2) -> (print_tipo_fn t1) ^ " -> " ^ (print_tipo_fn t2) 
		)

	let print_tipo s t : unit =
		(match t with 
			| TyInt-> Printf.printf "O tipo de %s é TyInt\n\n" s 
			| TyBool -> Printf.printf "O tipo de %s é TyBool\n\n" s 
			| TyFn(t1, t2) ->
				let tt1 = print_tipo_fn t1 in
				let tt2 = print_tipo_fn t2 in
				 Printf.printf "O tipo de %s é TyFn %s -> %s \n\n" s tt1 tt2
		)



(*
=====*=====*=====*=====*=====*=====
	EVAL: TESTES QUE DEVEM PASSAR
=====*=====*=====*=====*=====*=====
*)
	(* ==*== EXPRESSÕES ==*== *)

	(* ==*== Not ==*== *)
	let testNotOK = eval environment notOK;;
	print_value "Not(true)" testNotOK;;


	(* ==*== Bop ==*== *)
	(* 	Sub 	*)
	let testBopSubOK = eval environment bopSubOK;;
	print_value "Bop(Num(10), Sub, Num(5))" testBopSubOK;;

	(*	| Or 	*)
	let testBopOrOK = eval environment bopOrOK;;
	print_value "Bop(Bool(false), Or, Bool(true))" testBopOrOK;;

	(*	| Sum 	*)
	let testBopSumOK = eval environment bopSumOK;;
	print_value "Bop(Num(10), Sum, Num(5))" testBopSumOK;;

	(*	| Div 	*)
	let testBopDivOK = eval environment bopDivOK;;
	print_value "Bop(Num(10), Div, Num(5))" testBopDivOK;;

	(*	| And 	*)
	let testBopAndOK = eval environment bopAndOK;;
	print_value "Bop(Bool(false), And, Bool(true))" testBopAndOK;;

	(*	| Mult 	*)
	let testBopMultOK = eval environment bopMultOK;;
	print_value "Bop(Num(10), Mult, Num(5))" testBopMultOK;;

	(*	| Less 	*)
	let testBopLessOK = eval environment bopLessOK;;
	print_value "Bop(Num(10), Less, Num(5))" testBopLessOK;;

	(*	| Equal 	*)
	let testBopEqNumOK = eval environment bopEqNumOK;;
	print_value "Bop(Num(10), Equal, Num(5))" testBopEqNumOK;;

	let testBopEqBoolOK = eval environment bopEqBoolOK;;
	print_value "Bop(Bool(false), Equal, Bool(true))" testBopEqBoolOK;;

	(*	| Greater 	*)
	let testBopGreaterOK = eval environment bopGreaterOK;;
	print_value "Bop(Num(10), Greater, Num(5))" testBopGreaterOK;;

	(*	| NotEqual 	*)
	let testBopNotEqNumOK = eval environment bopNotEqNumOK;;
	print_value "Bop(Num(10), NotEqual, Num(5))" testBopNotEqNumOK;;

	let testBopNotEqBoolOK = eval environment bopNotEqBoolOK;;
	print_value "Bop(Bool(false), NotEqual, Bool(true))" testBopNotEqBoolOK;;

	(*	| LessOrEqual 	*)
	let testBopLessOrEqualOK = eval environment bopLessOrEqualOK;;
	print_value "Bop(Num(10), LessOrEqual, Num(5))" testBopLessOrEqualOK;;

	(*	| GreaterOrEqual 	*)
	let testBopGreaterOrEqualOK = eval environment bopGreaterOrEqualOK;;
	print_value "Bop(Num(10), GreaterOrEqual, Num(5))" testBopGreaterOrEqualOK;;


	(* ==*== IF ==*== *)
	let testIfFalse = eval environment ifFalse;;
	print_value "If(Bop(Num(99), NotEqual, Num(25)), Bool(true), Bool(false))" testIfFalse;;

	let testIfTrue = eval environment ifTrue;;
	print_value "If(Bop(Num(99), NotEqual, Num(25)), Bool(true), Bool(false))" testIfTrue;;


	(* ==*== FUNCTION ==*== *)
	let testFuncOK = eval environment funcOk;;
	print_value "Func(x, TyInt, Bop(Var(x), Sub, Num(1)))" testFuncOK;;


	(* ==*== APLICAÇÃO ==*== *)
	let testAppOk = eval environment appOK;;
	print_value "App(Func(x, TyInt, Bop(appVar, Sub, Num(4))), Num(5))" testAppOk;;


	(* ==*== LET ==*== *)
	let testLetOK01 = eval environment letOK01;;
	print_value "Let(x, TyInt, Num(2), Bop(Var(x), Sub, Num(2)))" testLetOK01;;

	let testLetOK02 = eval environment letOK02;;
	print_value "Let(x, TyInt, Num(2), Let(y, TyInt, Num(2), Bop(Var(x), Mult, Var(y))))" testLetOK02;;

	let testLetOK03 = eval environment letOK03;;
	print_value "Let(x, TyInt, Num(111), If(Bop(Var(x), Equal, Num(111)), Bool(true), Bool(false)))" testLetOK03;;


	(* ==*== LET REC ==*== *)
		(* ==*== EX. FATORIAL - FAT(10) ==*== *)
	let testLetRecOK01 = eval environment letRecOK01;;
	print_value "Fat(10)" testLetRecOK01;;

		(* ==*== EX. FIBONACCI - FIB(10)  ==*== *)
	let testLetRecOK02 = eval environment letRecOK02;;
	print_value "Fib(10)" testLetRecOK02;;


(*
=====*=====*=====*=====*=====*=====
	EVAL: TESTES QUE DEVEM DAR FAIL
=====*=====*=====*=====*=====*=====


	(* ==*== EXPRESSÕES ==*== *)

	(* ==*== Not ==*== *)
	let testNotFail = eval environment notFail;;


	(* ==*== Bop ==*== *)
	(* 	Sub 	*)
	let testBopSubFail = eval environment bopSubFail;;

	(*	| Or 	*)
	let testBopOrFail = eval environment bopOrFail;;

	(*	| Sum 	*)
	let testBopSumFail = eval environment bopSumFail;;

	(*	| Div 	*)
	let testBopDivFail = eval environment bopDivFail;;

	(*	| And 	*)
	let testBopAndFail = eval environment bopAndFail;;

	(*	| Mult 	*)
	let testBopMultFail = eval environment bopMultFail;;

	(*	| Less 	*)
	let testBopLessFail = eval environment bopLessFail;;

	(*	| Equal 	*)
	let testBopEqNumFail = eval environment bopEqNumFail;;

	let testBopEqBoolFail = eval environment bopEqBoolFail;;

	(*	| Greater 	*)
	let testBopGreaterFail = eval environment bopGreaterFail;;

	(*	| NotEqual 	*)
	let testBopNotEqNumFail = eval environment bopNotEqNumFail;;

	let testBopNotEqBoolFail = eval environment bopNotEqBoolFail;;

	(*	| LessOrEqual 	*)
	let testBopLessOrEqualFail = eval environment bopLessOrEqualFail;;

	(*	| GreaterOrEqual 	*)
	let testBopGreaterOrEqualFail = eval environment bopGreaterOrEqualFail;;


	(* ==*== IF ==*== *)
	let testIfFail = eval environment ifFalse;;

*)

(*
=====*=====*=====*=====*=====*=====
	TESTES
=====*=====*=====*=====*=====*=====
*)


	(* ==*== Ambiente vazio ==*== *)
 	let t_environment = t_emptyEnv;;
	
	(* ==*== Valores basicos ==*== *)
	let t_numTest = Vnum (5);;
	let t_boolTest = Vbool (true);;

	(* ==*== Estrutura do ambiente ==*== *)
	let t_envir = updateTEnv "numTest" TyInt t_environment;;
	searchTEnv "numTest" t_envir;;
	let t_envir' = updateTEnv "ten" TyInt t_envir;;
	let t_envir''= updateTEnv "numTest" TyInt t_envir';;
	searchTEnv "numTest" t_envir;;


	(* ==*== EXPRESSÕES ==*== *)

	(* ==*== Not ==*== *)
	let t_testNotOK = typecheck t_environment notOK;;
	print_tipo "Not(true)" t_testNotOK;;


	(* ==*== Bop ==*== *)
	(* 	Sub 	*)
	let t_testBopSubOK = typecheck t_environment bopSubOK;;
	print_tipo "Bop(Num(10), Sub, Num(5))" t_testBopSubOK;;

	(*	| Or 	*)
	let t_testBopOrOK = typecheck t_environment bopOrOK;;
	print_tipo "Bop(Bool(false), Or, Bool(true))" t_testBopOrOK;;

	(*	| Sum 	*)
	let t_testBopSumOK = typecheck t_environment bopSumOK;;
	print_tipo "Bop(Num(10), Sum, Num(5))" t_testBopSumOK;;

	(*	| Div 	*)
	let t_testBopDivOK = typecheck t_environment bopDivOK;;
	print_tipo "Bop(Num(10), Div, Num(5))" t_testBopDivOK;;

	(*	| And 	*)
	let t_testBopAndOK = typecheck t_environment bopAndOK;;
	print_tipo "Bop(Bool(false), And, Bool(true))" t_testBopAndOK;;

	(*	| Mult 	*)
	let t_testBopMultOK = typecheck t_environment bopMultOK;;
	print_tipo "Bop(Num(10), Mult, Num(5))" t_testBopMultOK;;

	(*	| Less 	*)
	let t_testBopLessOK = typecheck t_environment bopLessOK;;
	print_tipo "Bop(Num(10), Less, Num(5))" t_testBopLessOK;;

	(*	| Equal 	*)
	let t_testBopEqNumOK = typecheck t_environment bopEqNumOK;;
	print_tipo "Bop(Num(10), Equal, Num(5))" t_testBopEqNumOK;;

	let t_testBopEqBoolOK = typecheck t_environment bopEqBoolOK;;
	print_tipo "Bop(Bool(false), Equal, Bool(true))" t_testBopEqBoolOK;;

	(*	| Greater 	*)
	let t_testBopGreaterOK = typecheck t_environment bopGreaterOK;;
	print_tipo "Bop(Num(10), Greater, Num(5))" t_testBopGreaterOK;;

	(*	| NotEqual 	*)
	let t_testBopNotEqNumOK = typecheck t_environment bopNotEqNumOK;;
	print_tipo "Bop(Num(10), NotEqual, Num(5))" t_testBopNotEqNumOK;;

	let t_testBopNotEqBoolOK = typecheck t_environment bopNotEqBoolOK;;
	print_tipo "Bop(Bool(false), NotEqual, Bool(true))" t_testBopNotEqBoolOK;;

	(*	| LessOrEqual 	*)
	let t_testBopLessOrEqualOK = typecheck t_environment bopLessOrEqualOK;;
	print_tipo "Bop(Num(10), LessOrEqual, Num(5))" t_testBopLessOrEqualOK;;

	(*	| GreaterOrEqual 	*)
	let t_testBopGreaterOrEqualOK = typecheck t_environment bopGreaterOrEqualOK;;
	print_tipo "Bop(Num(10), GreaterOrEqual, Num(5))" t_testBopGreaterOrEqualOK;;


	(* ==*== IF ==*== *)
	let t_testIfFalse = typecheck t_environment ifFalse;;
	print_tipo "If(Bop(Num(99), NotEqual, Num(25)), Bool(true), Bool(false))" t_testIfFalse;;

	let t_testIfTrue = typecheck t_environment ifTrue;;
	print_tipo "If(Bop(Num(99), NotEqual, Num(25)), Bool(true), Bool(false))" t_testIfTrue;;


	(* ==*== FUNCTION ==*== *)
	let t_testFuncOK = typecheck t_environment funcOk;;
	print_tipo "Func(x, TyInt, Bop(Var(x), Sub, Num(1)))" t_testFuncOK;;


	(* ==*== APLICAÇÃO ==*== *)
	let t_testAppOk = typecheck t_environment appOK;;
	print_tipo "App(Func(x, TyInt, Bop(appVar, Sub, Num(4))), Num(5))" t_testAppOk;;


	(* ==*== LET ==*== *)
	let t_testLetOK01 = typecheck t_environment letOK01;;
	print_tipo "Let(x, TyInt, Num(2), Bop(Var(x), Sub, Num(2)))" t_testLetOK01;;

	let t_testLetOK02 = typecheck t_environment letOK02;;
	print_tipo "Let(x, TyInt, Num(2), Let(y, TyInt, Num(2), Bop(Var(x), Mult, Var(y))))" t_testLetOK02;;

	let t_testLetOK03 = typecheck t_environment letOK03;;
	print_tipo "Let(x, TyInt, Num(111), If(Bop(Var(x), Equal, Num(111)), Bool(true), Bool(false)))" t_testLetOK03;;


	(* ==*== LET REC ==*== *)
		(* ==*== EX. FATORIAL - FAT(10) ==*== *)
	let t_testLetRecOK01 = typecheck t_environment letRecOK01;;
	print_tipo "Fat(10)" t_testLetRecOK01;;

		(* ==*== EX. FIBONACCI - FIB(10)  ==*== *)
	let t_testLetRecOK02 = typecheck t_environment letRecOK02;;
	print_tipo "Fib(10)" t_testLetRecOK02;;


(*
=====*=====*=====*=====*=====*=====
	typecheck: TESTES QUE DEVEM DAR FAIL
=====*=====*=====*=====*=====*=====


	(* ==*== EXPRESSÕES ==*== *)

	(* ==*== Not ==*== *)
	let t_testNotFail = typecheck t_environment notFail;;


	(* ==*== Bop ==*== *)
	(* 	Sub 	*)
	let t_testBopSubFail = typecheck t_environment bopSubFail;;

	(*	| Or 	*)
	let t_testBopOrFail = typecheck t_environment bopOrFail;;

	(*	| Sum 	*)
	let t_testBopSumFail = typecheck t_environment bopSumFail;;

	(*	| Div 	*)
	let t_testBopDivFail = typecheck t_environment bopDivFail;;

	(*	| And 	*)
	let t_testBopAndFail = typecheck t_environment bopAndFail;;

	(*	| Mult 	*)
	let t_testBopMultFail = typecheck t_environment bopMultFail;;

	(*	| Less 	*)
	let t_testBopLessFail = typecheck t_environment bopLessFail;;

	(*	| Equal 	*)
	let t_testBopEqNumFail = typecheck t_environment bopEqNumFail;;

	let t_testBopEqBoolFail = typecheck t_environment bopEqBoolFail;;

	(*	| Greater 	*)
	let t_testBopGreaterFail = typecheck t_environment bopGreaterFail;;

	(*	| NotEqual 	*)
	let t_testBopNotEqNumFail = typecheck t_environment bopNotEqNumFail;;

	let t_testBopNotEqBoolFail = typecheck t_environment bopNotEqBoolFail;;

	(*	| LessOrEqual 	*)
	let t_testBopLessOrEqualFail = typecheck t_environment bopLessOrEqualFail;;

	(*	| GreaterOrEqual 	*)
	let t_testBopGreaterOrEqualFail = typecheck t_environment bopGreaterOrEqualFail;;


	(* ==*== IF ==*== *)
	let t_testIfFail = typecheck t_environment ifFalse;;

*)

(* 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= 
-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= 
-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= 
-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= 
-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= 
-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-= 
-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
*)


	(*
	=====*=====*=====*=====*=====*=====
		SSM2: ESTRUTURA 
	=====*=====*=====*=====*=====*=====
	*)

	type instruction =
		INT of int
		| BOOL of bool
		| POP
		| COPY
		| ADD
		| INV
		| EQ 
		| GT 
		| AND
		| OR
		| NOT
		| JUMP of int
		| JUMPIFTRUE of int
		| VAR of variable
		| FUN of variable * code
		| RFUN of variable * variable * code
		| APPLY
	and
		code = instruction list
	;;

	type storableValue =
		SVint of int
		| SVbool of bool
		| SVclos of cenv * variable * code
		| SVrclos of cenv * variable * variable * code
	and 
		stack = storableValue list
	and
		dump = (code * stack * cenv) list
	and
		cenv = (variable * storableValue) list
	;;

	type state = STATE of code * stack * cenv * dump
	;;


(* ==*== Atualizar o ambiente ==*== *)

	let updateCEnv variable v environment : cenv = match environment with
		|[] -> [(variable, v)]
		| hd::tl -> List.append [(variable, v)] environment

(* ==*== Busca no ambiente ==*== *)

	let rec searchCEnv variable environment : storableValue = match environment with
		| [] -> raise Not_found
		| (k, v)::tl ->
			if (k = variable)
			then v
			else searchCEnv variable tl

(* ==*== Ambiente vazio (usamos nos testes) ==*== *)

	let emptyCEnv : cenv = []


(*
=====*=====*=====*=====*=====*=====
	SSM2: COMPILAÇÃO DE L1
=====*=====*=====*=====*=====*=====
*)

	let rec compiler environment expr : code = match expr with
		| Num(n) -> [INT(n)]
		| Bool(b) -> [BOOL(b)]

		| Bop(e1, op, e2) -> 
			let exp1 = compiler environment e1 in
			let exp2 = compiler environment e2 in
			(match op with
				| Sub -> List.append (List.append exp2 (List.append [INV] exp1)) [ADD]
				| Or -> List.append exp2 (List.append exp1 [OR])
				| Sum -> List.append exp2 (List.append exp1 [ADD])
				| And -> List.append exp2 (List.append exp1 [AND])
				| Equal -> List.append exp2 (List.append exp1 [EQ])
				| Greater -> List.append exp2 (List.append exp1 [GT])

				(* ==*== caso de falha ==*== *)
				| _ -> failwith "bop_not_found"
			)
		| If(e1, e2, e3) -> 
			let exp1 = compiler environment e1 in
			let exp2 = compiler environment e2 in
			let exp3 = compiler environment e3 in
			let lengthE2 = List.length exp2 in
			let lengthE3 = List.length exp2 in (
				List.append
					(List.append
						(List.append
							exp1
							(List.append
								[JUMPIFTRUE(lengthE3 + 1)]
								exp3))
						[JUMP lengthE2])
					exp2
			)

		| Var(x) -> [VAR(x)]
		| App(e1, e2) -> 
			let exp1 = compiler environment e1 in
			let exp2 = compiler environment e2 in (
				List.append exp2 (List.append exp1 [APPLY])
			)

		| Func(variable, t, e) -> [FUN(variable, (compiler environment e))]

		| Let(variable, t, e1, e2) -> 
			let exp1 = compiler environment e1 in
			let exp2 = compiler environment e2 in (
				List.append exp1 (List.append [FUN(variable, exp2)] [APPLY])
			)

		| LetRec(f, (t1, t2), (var, t3, e1), e2) ->
			let exp1 = compiler environment e1 in
			let exp2 = compiler environment e2 in (
				[RFUN(f, var, exp1); FUN(f, exp2); APPLY]
			)

		| Not(e1) -> List.append (compiler environment e1) [NOT]
	;;


(*
=====*=====*=====*=====*=====*=====
	SSM2: INTERPRETAÇÃO
=====*=====*=====*=====*=====*=====
*)

	let rec split_at n l =
	 	if n = 0
	 	then ([], l)
	 	else
	  		(match l with
	  		| [] -> ([], [])    (*or raise an exception, as you wish*)
	  		| h :: t -> let (l1, l2) = split_at (n-1) t in (h :: l1, l2)
	  		)
	  	;;


	let rec interpreter c st e d : state = 
		match c with
			| [] -> 
				(match d with
					|[] -> STATE(c, st, e, d)
					| (c, s, e)::tl ->  interpreter c (List.append st s) e tl)

			| INT(n)::tl -> interpreter tl (List.append [SVint(n)] st) e d
			| BOOL(b)::tl -> interpreter tl (List.append [SVbool(b)] st) e d

			| POP::tl ->
				(match st with
					|[] -> failwith "POP: EMPTY STACK"
					| hd::rest -> interpreter tl rest e d)

			| COPY::tl -> 
				(match st with
					|[] -> failwith "COPY: EMPTY STACK"
					| hd::rest -> interpreter tl (List.append [hd] st) e d)

			| ADD::tl -> 
				(match st with
					|[] -> failwith "ADD: EMPTY STACK"
					| SVint(z1)::rest ->
						(match rest with
							|[] -> failwith "ADD: STACK HAS ONLY ONE STORABLE VALUE"
							| SVint(z2)::rest2 -> interpreter tl (List.append [SVint(z1 + z2)] rest2) e d
							| _ -> failwith "ADD: NOT AN INT"
						)
					| _ -> failwith "ADD: NOT AN INT" 
				)

			| INV::tl ->
				(match st with
						|[] -> failwith "INV: EMPTY STACK"
						| SVint(z1)::rest -> interpreter tl (List.append [SVint(z1 - z1 - z1)] rest) e d
						| _ -> failwith "INV: NOT AN INT"
				)

			| EQ::tl ->				
				(match st with
					|[] -> failwith "EQ: EMPTY STACK"
					| SVint(z1)::rest ->
						(match rest with
							|[] -> failwith "EQ: STACK HAS ONLY ONE STORABLE VALUE"
							| SVint(z2)::rest2 -> interpreter tl (List.append [SVbool(z1 == z2)] rest2) e d
							| _ -> failwith "EQ: NOT INT or BOOL"
						)
					| SVbool(z1)::rest ->
						(match rest with
							|[] -> failwith "EQ: STACK HAS ONLY ONE STORABLE VALUE"
							| SVbool(z2)::rest2 -> interpreter tl (List.append [SVbool(z1 == z2)] rest2) e d
							| _ -> failwith "EQ: NOT INT or BOOL"
						)
					| _ -> failwith "EQ: NOT INT or BOOL" 
				)

			| GT::tl -> 
				(match st with
					|[] -> failwith "GT: EMPTY STACK"
					| SVint(z1)::rest ->
						(match rest with
							|[] -> failwith "GT: STACK HAS ONLY ONE STORABLE VALUE"
							| SVint(z2)::rest2 -> interpreter tl (List.append [SVbool(z1 > z2)] rest2) e d
							| _ -> failwith "GT: NOT AN INT"
						)
					| _ -> failwith "GT: NOT AN INT" 
				)

			| AND::tl -> 
				(match st with
					|[] -> failwith "AND: EMPTY STACK"
					| SVbool(z1)::rest ->
						(match rest with
							|[] -> failwith "AND: STACK HAS ONLY ONE STORABLE VALUE"
							| SVbool(z2)::rest2 -> interpreter tl (List.append [SVbool(z1 && z2)] rest2) e d
							| _ -> failwith "AND: NOT AN BOOL"
						)
					| _ -> failwith "AND: NOT AN BOOL" 
				)

			| OR::tl -> 
				(match st with
					|[] -> failwith "OR: EMPTY STACK"
					| SVbool(z1)::rest ->
						(match rest with
							|[] -> failwith "OR: STACK HAS ONLY ONE STORABLE VALUE"
							| SVbool(z2)::rest2 -> interpreter tl (List.append [SVbool(z1 || z2)] rest2) e d
							| _ -> failwith "OR: NOT AN BOOL"
						)
					| _ -> failwith "OR: NOT AN BOOL" 
				)

			| NOT::tl -> 
				(match st with
						|[] -> failwith "NOT: EMPTY STACK"
						| SVbool(z1)::rest -> interpreter tl (List.append [SVbool(not(z1))] rest) e d
						| _ -> failwith "POP: NOT AN INT"
				)

			| JUMP(n)::tl -> 
				let (l1, l2) = split_at n c in
				(interpreter l2 st e d)

			| JUMPIFTRUE(n)::tl -> 
				let (l1, l2) = split_at n c in
				(match st with
						|[] -> failwith "JUMPIFTRUE: EMPTY STACK"
						| SVbool(z1)::rest -> 
							(if z1
							then (interpreter l2 rest e d)
							else (interpreter tl rest e d))
						| _ -> failwith "JUMPIFTRUE: NOT A BOOL"
				)

			| VAR(x)::tl -> interpreter tl (List.append [(searchCEnv x e)] st) e d

			| FUN(x, cod)::tl -> interpreter tl (List.append [SVclos(e, x, cod)] st) e d

			| APPLY::tl -> 
				(match st with
					|[] -> failwith "APPLY: EMPTY STACK"
					| SVclos(e', x, c')::rest ->
						(match rest with
							|[] -> failwith "APPLY: STACK HAS ONLY ONE STORABLE VALUE"
							| hd::rest2 -> interpreter c' [] (updateCEnv x hd e')  (List.append [(c, st, e)] d)
						)
					| SVrclos(e', f, x, c')::rest ->
						(match rest with
							|[] -> failwith "APPLY: STACK HAS ONLY ONE STORABLE VALUE"
							| hd::rest2 -> interpreter c' [] (updateCEnv f (SVrclos(e', f, x, c')) (updateCEnv x hd e')) (List.append [(c, st, e)] d)
						)
					| _ -> failwith "OR: NOT A CLOSURE" )

			| RFUN(f, x, cod)::tl -> interpreter tl (List.append [SVrclos(e, f, x, cod)] st) e d
	;;