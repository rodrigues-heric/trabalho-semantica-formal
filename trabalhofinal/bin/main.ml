(** Branch de estudos de OCaml *)

(*
  https://ocaml.org/exercises?difficulty_level=beginner   
*)

(*
  Comandos úteis
  - dune build __nomeprojeto__ -> compila o projeto
  - dune exec __nomeprojeto__ -> executa o projeto compilado
  - dune fmt -> formata os arquivos do projeto   
*)

(*
   Infos úteis
   - Uma lista sempre é uma lista encadeada do tipo (elemento [resto da lista])
   - O identificador _ é o default no loop (switch ... case ... default)
   - O operador :: é uma das opções de lista ([_, tail] == _ :: tail)
   - O operador @ é utilizado para concatenar listas
   - O separador de uma lista é ; e não ,
*)

(** Tail of list *)
let rec last : 'a list -> 'a option = function
  | [] -> None
  | [ x ] -> Some x
  | _ :: tail -> last tail
;;

last [ "a"; "b"; "c" ]

(** Last two elements of a list *)
let rec last_two : 'a list -> ('a * 'a) option = function
  | [] | [ _ ] -> None
  | [ x; y ] -> Some (x, y)
  | _ :: tail -> last_two tail
;;

last_two [ "a"; "b"; "c"; "d"; "e" ]

(** N'th element of a list *)
let rec nth_element k = function
  | [] -> None
  | head :: tail -> if k = 0 then Some head else nth_element (k - 1) tail
;;

nth_element 2 [ "a"; "b"; "c" ]

(** Length of a list *)
let rec list_length : 'a list -> int = function
  | [] -> 0
  | _ :: tail -> 1 + list_length tail
;;

list_length [ "a"; "b"; "c" ]

(** Reverse a list *)
let rec list_reverse : 'a list -> 'b list = function
  | [] -> []
  | x :: tail -> list_reverse tail @ [ x ]
;;

list_reverse [ "a"; "b"; "c" ]

(** Palindrome *)
let is_palindrome (list_to_check : 'a list) : bool =
  list_to_check = list_reverse list_to_check
;;

is_palindrome [ "o"; "v"; "o" ]

(** Duplicate the elements of a list *)
let rec double_list_elements : 'a list -> 'b list = function
  | [] -> []
  | head :: tail -> head :: head :: double_list_elements tail
;;

double_list_elements [ ("a", "b") ]
