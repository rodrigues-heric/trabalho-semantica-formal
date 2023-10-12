(** Branch de estudos de OCaml *)

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
*)

(** Write a function last : 'a list -> 'a option that returns the last element of a list *)
let rec last : 'a list -> 'a option = function
  | [] -> None
  | [ x ] -> Some x
  | _ :: tail -> last tail
;;

last [ ("a", "b", "c") ]

(** Last two elements of a list *)
let rec last_two : 'a list -> ('a * 'a) option = function
  | [] | [ _ ] -> None
  | [ x; y ] -> Some (x, y)
  | _ :: tail -> last_two tail
;;

last_two [ ("a", "b", "c", "d", "e") ]

(** N'th element of a list *)
let rec nth_element k = function
  | [] -> None
  | head :: tail -> if k = 0 then Some head else nth_element (k - 1) tail
;;

nth_element 2 [ ("a", "b", "c") ]
