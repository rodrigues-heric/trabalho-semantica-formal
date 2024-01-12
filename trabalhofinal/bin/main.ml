(** Trabalho da disciplina Semântica Formal *)

(** Tipos de L1 *)
type l1_type =
  | L1Int
  | L1Bool
  | L1Fn of l1_type * l1_type
  | L1Pair of l1_type * l1_type

type identifier = string
(** Identificador de variáveis de tipos de L1 *)

(** Operadores binários de L1 *)
type operator = Sum | Sub | Mult | Equal | Greater | Less | GreaterEq | LessEq

(** Expressões de L1 *)
type expression =
  | Num of int
  | Var of identifier
  | True
  | False
  | BiOperator of operator * expression * expression
  | Pair of expression * expression
  | First of expression
  | Second of expression
  | If of expression * expression * expression
  | Func of identifier * l1_type * expression
  | App of expression * expression
  | Let of identifier * l1_type * expression * expression
  | LetRec of identifier * l1_type * expression * expression

type environment = (identifier * l1_type) list
(** Ambiente de L1 *)

let empty_env : environment = []

let rec lookup (env : environment) (x : identifier) : l1_type option =
  match env with
  | [] -> None
  | (y, t) :: env' -> if x = y then Some t else lookup env' x

let rec update (env : environment) (x : identifier) (t : l1_type) : environment
    =
  (x, t) :: env

exception L1TypeError of string
(** Exceções de L1 *)

(** Inferência de tipos de L1 *)
let rec l1_type_infer (env : environment) (e : expression) : l1_type =
  match e with
  | Num _ -> L1Int
  | Var x -> (
      match lookup env x with
      | None -> raise (L1TypeError "Variável não declarada")
      | Some t -> t)
  | True -> L1Bool
  | False -> L1Bool
  | BiOperator (op, e1, e2) ->
      let t1 = l1_type_infer env e1 in
      let t2 = l1_type_infer env e2 in
      if t1 = L1Int && t2 = L1Int then
        match op with
        | Sum | Sub | Mult -> L1Int
        | Equal | Greater | Less | GreaterEq | LessEq -> L1Bool
      else raise (L1TypeError "Operador binário aplicado a tipos não inteiros")
  | Pair (e1, e2) -> L1Pair (l1_type_infer env e1, l1_type_infer env e2)
  | First e -> (
      match l1_type_infer env e with
      | L1Pair (t1, _) -> t1
      | _ -> raise (L1TypeError "First aplicado a expressão não par"))
  | Second e -> (
      match l1_type_infer env e with
      | L1Pair (_, t2) -> t2
      | _ -> raise (L1TypeError "Second aplicado a expressão não par"))
  | If (e1, e2, e3) -> (
      match l1_type_infer env e1 with
      | L1Bool ->
          let t2 = l1_type_infer env e2 in
          let t3 = l1_type_infer env e3 in
          if t2 = t3 then t2
          else raise (L1TypeError "Tipos de expressões do if não são iguais")
      | _ -> raise (L1TypeError "If aplicado a expressão não booleana"))
  | Func (x, t, e) -> L1Fn (t, l1_type_infer (update env x t) e)
  | App (e1, e2) -> (
      match l1_type_infer env e1 with
      | L1Fn (t1, t2) ->
          let t3 = l1_type_infer env e2 in
          if t1 = t3 then t2
          else raise (L1TypeError "Argumento da função não é do tipo esperado")
      | _ -> raise (L1TypeError "Aplicação de função a expressão não função"))
  | Let (x, t, e1, e2) ->
      if l1_type_infer env e1 = t then l1_type_infer (update env x t) e2
      else raise (L1TypeError "Tipo da expressão não é o esperado")
  | LetRec (x, (L1Fn (_t1, t2) as type_func), Func (y, ty, e1), e2) ->
      let env' = update env x type_func in
      let env'' = update env' y ty in
      if l1_type_infer env'' e1 = t2 then l1_type_infer env' e2
      else raise (L1TypeError "Tipo da expressão não é o esperado")
  | _ -> raise (L1TypeError "Expressão não implementada. Erro no parser.")

(** Avaliador Big-Step com substituição de L1 *)
let replace (v : expression) (x : identifier) (e : expression) : expression =
  let rec rp (e : expression) : expression =
    match e with
    | Num _ -> e
    | True -> e
    | False -> e
    | BiOperator (operator, e1, e2) -> BiOperator (operator, rp e1, rp e2)
    | App (e1, e2) -> App (rp e1, rp e2)
    | Pair (e1, e2) -> Pair (rp e1, rp e2)
    | First e1 -> First (rp e1)
    | Second e1 -> Second (rp e1)
    | If (e1, e2, e3) -> If (rp e1, rp e2, rp e3)
    | Var y -> if x = y then v else e
    | Func (y, t, e1) -> if x = y then e else Func (y, t, rp e1)
    | Let (y, t, e1, e2) -> Let (y, t, rp e1, rp e2)
    | LetRec (f, tf, ef, e2) -> if x = f then e else LetRec (f, tf, rp ef, rp e2)
  in
  rp e

(** Avaliação em L1 *)
let compute (operator : operator) (v1 : expression) (v2 : expression) =
  match (operator, v1, v2) with
  | Sum, Num n1, Num n2 -> Num (n1 + n2)
  | Sub, Num n1, Num n2 -> Num (n1 - n2)
  | Mult, Num n1, Num n2 -> Num (n1 * n2)
  | Equal, Num n1, Num n2 -> if n1 = n2 then True else False
  | Greater, Num n1, Num n2 -> if n1 > n2 then True else False
  | Less, Num n1, Num n2 -> if n1 < n2 then True else False
  | GreaterEq, Num n1, Num n2 -> if n1 >= n2 then True else False
  | LessEq, Num n1, Num n2 -> if n1 <= n2 then True else False
  | _ -> raise (L1TypeError "Operador binário aplicado a tipos não inteiros")

let rec evaluate (e : expression) =
  match e with
  | Num _ -> e
  | Var _x -> raise (L1TypeError "Variável não declarada")
  | True -> e
  | False -> e
  | BiOperator (operator, e1, e2) ->
      compute operator (evaluate e1) (evaluate e2)
  | Pair (e1, e2) -> Pair (evaluate e1, evaluate e2)
  | First e1 -> (
      match evaluate e1 with
      | Pair (e1, _) -> e1
      | _ -> raise (L1TypeError "First aplicado a expressão não par"))
  | Second e1 -> (
      match evaluate e1 with
      | Pair (_, e2) -> e2
      | _ -> raise (L1TypeError "Second aplicado a expressão não par"))
  | If (e1, e2, e3) -> (
      match evaluate e1 with
      | True -> evaluate e2
      | False -> evaluate e3
      | _ -> raise (L1TypeError "If aplicado a expressão não booleana"))
  | Func _ -> e
  | App (e1, e2) -> (
      match evaluate e1 with
      | Func (x, _, e) -> evaluate (replace (evaluate e2) x e)
      | _ -> raise (L1TypeError "Aplicação de função a expressão não função"))
  | Let (x, t, e1, e2) -> evaluate (App (Func (x, t, e2), e1))
  | LetRec
      (f, (L1Fn (t1, _t2) as type_func), (Func (x, tx, e1) as type_body), e2)
    when t1 = tx ->
      let alpha = Func (x, t1, LetRec (f, type_func, type_body, e1)) in
      evaluate (replace alpha f e2)
  | _ -> raise (L1TypeError "Expressão não implementada. Erro no parser.")

(** Interpretador para L1 *)
let rec is_value (e : expression) : bool =
  match e with
  | Num _ -> true
  | True -> true
  | False -> true
  | Pair (e1, e2) -> is_value e1 && is_value e2
  | Func _ -> true
  | _ -> false

let rec value_to_string (e : expression) : string =
  match e with
  | Num n -> string_of_int n
  | True -> "true"
  | False -> "false"
  | Pair (e1, e2) -> "(" ^ value_to_string e1 ^ ", " ^ value_to_string e2 ^ ")"
  | Func _ -> "<fun>"
  | _ -> raise (L1TypeError "Expressão não implementada. Erro no parser.")

let rec type_to_string (t : l1_type) : string =
  match t with
  | L1Int -> "int"
  | L1Bool -> "bool"
  | L1Fn (t1, t2) -> type_to_string t1 ^ " -> " ^ type_to_string t2
  | L1Pair (t1, t2) -> "(" ^ type_to_string t1 ^ " * " ^ type_to_string t2 ^ ")"

let interpreter (e : expression) : unit =
  try
    let t = l1_type_infer empty_env e in
    let v = evaluate e in
    print_string (value_to_string v ^ " : " ^ type_to_string t ^ "\n")
  with L1TypeError s -> print_string ("Erro de tipo: " ^ s ^ "\n")

(* Testes *)
let upd1 = update empty_env "x" L1Int
let upd2 = update upd1 "y" L1Bool
let upd3 = update upd2 "x" L1Bool
let testerec = LetRec ("f", L1Int, Num 5, Num 5)

(* run: l1_type_infer [] testerec => Erro proposital *)
let testeif = If (First (Num 5), Num 10, Num 20)

(* run: l1_type_infer [] testif => Erro proposital *)
let testeop = BiOperator (Mult, True, Num 5)
(* run: l1_type_infer [] testeop => Erro proposital *)

(* x ^y *)
let x_pow_y = BiOperator (Sub, Var "y", Num 1)
let pow_app = App (App (Var "pow", Var "x"), x_pow_y)
let x_pow = BiOperator (Mult, Var "x", pow_app)
