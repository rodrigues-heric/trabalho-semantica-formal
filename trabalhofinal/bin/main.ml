(** Trabalho da disciplina Semântica Formal *)

(** Grupo:
  - Heric Leite Rodrigues 
  - Joana Campos
*)

(** A linaguagem L2
A linguagem L2 é uma extensão da linguagem L1 com construções imperativas para alocar, ler e escrever
na memória. L2 também possui novas construções para controle do fluxo de execução (para sequência e
repetição).
*)

(* Exceções de L2 *)
exception BugParser
exception BugTypeInfer
exception TypeError of string

(** Tipoes de L2

  TyInt ->> tipo dos números inteiros

  TyBool ->> tipo dos booleanos

  TyFn ->> tipo das funções
  
  TyPair ->> tipo dos pares
*)
type tipo = TyInt | TyBool | TyFn of tipo * tipo | TyPair of tipo * tipo

type ident = string
(** Identificadores de L2
  
ident ->> conjunto dos identificadores
*)

(** Operadores de L2

Sum ->> Soma 

Sub ->> Subtração 

Mult ->> Multiplicação

Eq ->> Igualdade 

Gt ->> Maior que

Lt ->> Menor que

Geq ->> Maior ou igual que 

Leq ->> Menor ou igual que
*)
type op = Sum | Sub | Mult | Eq | Gt | Lt | Geq | Leq

(** Expressões de L2
e ::= 
  | n 
  | b 
  | e1 op e2 
  | if e1 then e2 else e3 
  | e1 := e2 ->> e1 local de memória, e2 valor a ser armazenado
  | !e1 ->> acessar o valor armazenado no local de memória e1
  | new e1 ->> alocar um novo local de memória e inicializar com o valor de e1
  | l 
  | skip 
  | e1 ; e2 
  | while e1 do e2 
  | fn x:T -> e 
  | e1 e2 
  | x 
  | let x:T = e1 in e2 
  | let rec f:T1 -> T2 = (fn y:T1 -> e1) in e2 
onde 
  n ->> conjunto dos números inteiros 
  b ->> conjunto dos booleanos
  op ->> conjunto dos operadores aritméticos e relacionais  
  l ->> conjunto dos endereços de memória
*)
type expr =
  | Num of int
  | Var of ident
  | True
  | False
  | Binop of op * expr * expr
  | Pair of expr * expr
  | Fst of expr
  | Snd of expr
  | If of expr * expr * expr
  | Fn of ident * tipo * expr
  | App of expr * expr
  | Let of ident * tipo * expr * expr
  | LetRec of ident * tipo * expr * expr

type tenv = (ident * tipo) list
(** Ambiente de L2 *)

(** Valores de L2 
    
VNum ->> valor dos números inteiros

VTrue ->> valor verdadeiro

VFalse ->> valor falso

VPair ->> valor dos pares

VClos ->> valor das funções (closure)

VRClos ->> valor das funções recursivas (recursive closure)
*)
type valor =
  | VNum of int
  | VTrue
  | VFalse
  | VPair of valor * valor
  | VClos of ident * expr * renv
  | VRClos of ident * ident * expr * renv

and renv = (ident * valor) list

(* Funções auxiliares *)
let rec lookup env key =
  match env with
  | [] -> None
  | (index, value) :: tail ->
      if index = key then Some value else lookup tail key

let rec update env key value = (key, value) :: env

let rec ttos (t : tipo) : string =
  match t with
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyFn (t1, t2) -> "(" ^ ttos t1 ^ " -> " ^ ttos t2 ^ ")"
  | TyPair (t1, t2) -> "(" ^ ttos t1 ^ " * " ^ ttos t2 ^ ")"

let rec vtos (v : valor) : string =
  match v with
  | VNum n -> string_of_int n
  | VTrue -> "true"
  | VFalse -> "false"
  | VPair (v1, v2) -> "(" ^ vtos v1 ^ ", " ^ vtos v2 ^ ")"
  | VClos _ -> "<fun>"
  | VRClos _ -> "<fun>"

(** Inferência de tipos para L2 *)
let rec typeinfer (tenv : tenv) (e : expr) : tipo =
  match e with
  | Num _ -> TyInt
  | Var x -> (
      match lookup tenv x with
      | Some t -> t
      | None -> raise (TypeError ("Variável não declarada: " ^ x)))
  | True -> TyBool
  | False -> TyBool
  | Binop (oper, e1, e2) ->
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in
      if t1 = TyInt && t2 = TyInt then
        match oper with
        | Sum | Sub | Mult -> TyInt
        | Eq | Gt | Lt | Geq | Leq -> TyBool
      else raise (TypeError "Operação inválida")
  | Pair (e1, e2) -> TyPair (typeinfer tenv e1, typeinfer tenv e2)
  | Fst e1 -> (
      match typeinfer tenv e1 with
      | TyPair (t1, _t2) -> t1
      | _ -> raise (TypeError "Fst espera um par"))
  | Snd e1 -> (
      match typeinfer tenv e1 with
      | TyPair (_t1, t2) -> t2
      | _ -> raise (TypeError "Snd espera um par"))
  | If (e1, e2, e3) -> (
      match typeinfer tenv e1 with
      | TyBool ->
          let t2 = typeinfer tenv e2 in
          let t3 = typeinfer tenv e3 in
          if t2 = t3 then t2
          else raise (TypeError "Tipos diferentes para then e else")
      | _ -> raise (TypeError "If espera um booleano"))
  | Fn (x, t, e1) ->
      let t1 = typeinfer (update tenv x t) e1 in
      TyFn (t, t1)
  | App (e1, e2) -> (
      match typeinfer tenv e1 with
      | TyFn (t, t') ->
          if typeinfer tenv e2 = t then t'
          else raise (TypeError "Tipos diferentes para aplicação")
      | _ -> raise (TypeError "Aplicação espera uma função"))
  | Let (x, t, e1, e2) ->
      if typeinfer tenv e1 = t then typeinfer (update tenv x t) e2
      else raise (TypeError "Tipos diferentes para let")
  | LetRec (f, (TyFn (_t1, t2) as tf), Fn (x, tx, e1), e2) ->
      let tenv' = update tenv f tf in
      let tenv'' = update tenv' x tx in
      if typeinfer tenv'' e1 = t2 then typeinfer tenv' e2
      else raise (TypeError "Tipos diferentes para let rec")
  | _ -> raise BugParser

(** Avaliador de L2 *)
let compute (oper : op) (v1 : valor) (v2 : valor) =
  match (oper, v1, v2) with
  | Sum, VNum n1, VNum n2 -> VNum (n1 + n2)
  | Sub, VNum n1, VNum n2 -> VNum (n1 - n2)
  | Mult, VNum n1, VNum n2 -> VNum (n1 * n2)
  | Eq, VNum n1, VNum n2 -> if n1 = n2 then VTrue else VFalse
  | Gt, VNum n1, VNum n2 -> if n1 > n2 then VTrue else VFalse
  | Lt, VNum n1, VNum n2 -> if n1 < n2 then VTrue else VFalse
  | Geq, VNum n1, VNum n2 -> if n1 >= n2 then VTrue else VFalse
  | Leq, VNum n1, VNum n2 -> if n1 <= n2 then VTrue else VFalse
  | _ -> raise BugTypeInfer

let rec eval (renv : renv) (e : expr) : valor =
  match e with
  | Num n -> VNum n
  | True -> VTrue
  | False -> VFalse
  | Var x -> (
      match lookup renv x with Some v -> v | None -> raise BugTypeInfer)
  | Binop (oper, e1, e2) ->
      let v1 = eval renv e1 in
      let v2 = eval renv e2 in
      compute oper v1 v2
  | Pair (e1, e2) ->
      let v1 = eval renv e1 in
      let v2 = eval renv e2 in
      VPair (v1, v2)
  | Fst e -> (
      match eval renv e with VPair (v1, _) -> v1 | _ -> raise BugTypeInfer)
  | Snd e -> (
      match eval renv e with VPair (_, v2) -> v2 | _ -> raise BugTypeInfer)
  | If (e1, e2, e3) -> (
      match eval renv e1 with
      | VTrue -> eval renv e2
      | VFalse -> eval renv e3
      | _ -> raise BugTypeInfer)
  | Fn (x, _t, e1) -> VClos (x, e1, renv)
  | App (e1, e2) -> (
      let v1 = eval renv e1 in
      let v2 = eval renv e2 in
      match v1 with
      | VClos (x, body, renv') ->
          let renv'' = update renv' x v2 in
          eval renv'' body
      | VRClos (f, x, body, renv') ->
          let renv'' = update renv' x v2 in
          let renv''' = update renv'' f v1 in
          eval renv''' body
      | _ -> raise BugTypeInfer)
  | Let (x, _t, e1, e2) ->
      let v1 = eval renv e1 in
      eval (update renv x v1) e2
  | LetRec (f, TyFn (t1, _t2), Fn (x, tx, e1), e2) when t1 = tx ->
      let renv' = update renv f (VRClos (f, x, e1, renv)) in
      eval renv' e2
  | _ -> raise BugTypeInfer

(** Interpretador de L2 *)
let int_bse (e : expr) =
  try
    let t = typeinfer [] e in
    let v = eval [] e in
    print_string (vtos v ^ " : " ^ ttos t)
  with
  | TypeError msg -> print_string ("TypeError: " ^ msg)
  | BugTypeInfer -> print_string "Erro presente no typeinfer"
  | BugParser -> print_string "Erro presente no parser"
