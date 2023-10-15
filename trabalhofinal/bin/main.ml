(** Interpretador da Linguagem L0 *)

(**
  Gramática:

  e ::= true | false | if(e1,e2,e3) | 0 | succ(e) | pred(e) | iszero (e)
*)
type expr =
  | ExTrue
  | ExFalse
  | ExIf of expr * expr * expr
  | ExZero
  | ExSucc of expr
  | ExPred of expr
  | ExIsZero of expr

(* Exceções *)
exception NoRuleApplies

(* Funções auxiliares *)

(** Verifica se a expressão um valor é numérico *)
let rec isNumericValue (e : expr) : bool =
  match e with ExZero -> true | ExSucc e1 -> isNumericValue e1 | _ -> false

(** Avança um passo na execução da AST *)
let rec step (e : expr) : expr =
  match e with
  (* Casos if *)
  | ExIf (ExTrue, e2, _) -> e2
  | ExIf (ExFalse, _, e3) -> e3
  | ExIf (e1, e2, e3) ->
      let e1' = step e1 in
      ExIf (e1', e2, e3)
  (* Caso succ *)
  | ExSucc e1 ->
      let e1' = step e1 in
      ExSucc e1'
  (* Caso pred *)
  | ExPred ExZero -> ExZero
  | ExPred (ExSucc nv) when isNumericValue nv -> nv
  | ExPred e1 ->
      let e1' = step e1 in
      ExPred e1'
  (* Caso iszero *)
  | ExIsZero ExZero -> ExTrue
  | ExIsZero (ExSucc nv) when isNumericValue nv -> ExFalse
  | ExIsZero e1 ->
      let e1' = step e1 in
      ExIsZero e1'
  (* Nenhuma regra se aplica *)
  | _ -> raise NoRuleApplies

(** Avalia uma empressão *)
let rec eval (e : expr) : expr =
  try
    let e' = step e in
    eval e'
  with NoRuleApplies -> e

(** Verifica se é uma forma normal *)
let isNormalForm (e : expr) : bool =
  isNumericValue e || e = ExTrue || e = ExFalse
