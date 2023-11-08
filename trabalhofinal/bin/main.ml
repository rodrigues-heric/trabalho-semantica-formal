(** Compilador para SSM0 *)

(** expressoes da linguagem L0 *)
type expr =
  | ExTrue
  | ExFalse
  | ExIf of expr * expr * expr
  | ExZero
  | ExSucc of expr
  | ExPred of expr
  | ExIsZero of expr
  | ExAnd of expr * expr
  | ExOr of expr * expr
  | ExNot of expr

(** instruções da máquina abstrata SSM0 *)
type instr = PUSH of int | POP | COPY | INC | DEC | JMP of int | JMPZR of int

type ssm0 = instr list
type stack = int list
type state = ssm0 * stack

exception ExceptionInvalidArg
exception ExceptionEndOfProg
exception ExceptionJmpOutOfProg
exception ExceptionEmptyStack

(*** retorna lista sem os seus n primeiros elementos *)
let rec drop n l =
  if n < 0 then raise ExceptionInvalidArg
  else
    match (n, l) with
    | 0, _ -> Some l
    | n, _ :: t -> drop (n - 1) t
    | _, [] -> None

let step : state -> state = function
  | [], _ -> raise ExceptionEndOfProg
  | PUSH z :: code, stack -> (code, z :: stack)
  | JMP n :: code, stack -> (
      match drop n code with
      | Some code' -> (code', stack)
      | None -> raise ExceptionJmpOutOfProg)
  | POP :: code, _ :: stack -> (code, stack)
  | COPY :: code, z :: stack -> (code, z :: z :: stack)
  | INC :: code, z :: stack -> (code, (z + 1) :: stack)
  | DEC :: code, z :: stack -> (code, (z - 1) :: stack)
  | JMPZR n :: code, 0 :: stack -> (
      match drop n code with
      | Some code' -> (code', stack)
      | None -> raise ExceptionJmpOutOfProg)
  | JMPZR _ :: code, _ :: stack -> (code, stack)
  | POP :: _, [] -> raise ExceptionEmptyStack
  | COPY :: _, [] -> raise ExceptionEmptyStack
  | INC :: _, [] -> raise ExceptionEmptyStack
  | DEC :: _, [] -> raise ExceptionEmptyStack
  | JMPZR _ :: _, [] -> raise ExceptionEmptyStack

let rec eval c =
  try
    let c' = step c in
    eval c'
  with
  | ExceptionJmpOutOfProg -> ("jmp fora do programa", c)
  | ExceptionEndOfProg -> ("fim normal", c)
  | ExceptionEmptyStack -> ("op com pilha vazia", c)
  | ExceptionInvalidArg -> ("desvio com argumento negativo", c)

(*** função de compilação de ASTs de L0 para programa SSM0 *)
let rec comp (e : expr) : ssm0 =
  match e with
  | ExTrue -> [ PUSH 1 ]
  | ExFalse -> [ PUSH 0 ]
  | ExZero -> [ PUSH 0 ]
  | ExSucc e1 -> comp e1 @ [ INC ]
  | ExPred e1 -> comp e1 @ [ COPY; JMPZR 1; DEC ]
  | ExIsZero e1 -> comp e1 @ [ JMPZR 2; PUSH 0; JMP 1; PUSH 1 ]
  | ExIf (e1, e2, e3) ->
      let c2 = comp e2 in
      let c3 = comp e3 in
      let n2 = List.length c2 in
      let n3 = List.length c3 in
      comp e1 @ [ JMPZR (n2 + 1) ] @ c2 @ [ JMP n3 ] @ c3
  | ExAnd (e1, e2) ->
      let c1 = comp e1 in
      let c2 = comp e2 in
      let n2 = List.length c2 in
      c1 @ [ JMPZR (n2 + 3) ] @ c2 @ [ JMPZR 2; PUSH 1; PUSH 0 ]
  | ExOr (e1, e2) ->
      let c1 = comp e1 in
      let c2 = comp e2 in
      let n2 = List.length c2 in
      c1 @ [ JMPZR 2; PUSH 1; JMP (n2 + 4) ] @ c2 @ [ JMPZR 2; PUSH 1; PUSH 0 ]
  | ExNot e -> comp e @ [ JMPZR 2; PUSH 0; JMP 1; PUSH 1 ]
