(* 1. fib *)

let rec fib : int -> int
= fun n -> 
  match n with
    | 0 -> 0
    | 1 -> 1
    | _ -> fib (n-1) + fib (n-2);;

(* 2. pascal *)

let rec pascal : int * int -> int
= fun (n, m) -> 
  if n = m then 1 else
      match (n, m) with
        | (_, 0) -> 1
        | (_, _) -> pascal (n-1, m-1) + pascal (n-1, m);;

(* 3. prime *)

let rec func x n =
if x = 1 then 1 else (match x with
| 0 -> 0
| _ -> if x >= n then (func (x-1) n) else 
(if n mod x = 0 then 0 else (func (x-1) n)));;

let prime : int -> bool
= fun n ->
  match n with
    |2 -> true
    |_ -> if (func n n) = 1 then true else false;;

(* Feedback *)

let rec prime_aux : int -> int -> bool
= fun n d ->
  if d * d > n then 
    true 
  else if n mod d = 0 then 
    false 
  else prime_aux n (d + 1)

let prime : int -> bool
= fun n -> if n = 1 then false else prime_aux n 2

(* 4. dfact *)

let rec dfact : int -> int
= fun n -> if n mod 2 = 0 then (match n with
  | 2 -> 2
  | _ -> n * dfact (n-2)) else (match n with
    | 1 -> 1
    | _ -> n * dfact (n-2));;

(* 5. fastexpt *)

let rec fastexpt : int -> int -> int 
= fun b n -> if n = 0 then 1 
else if n mod 2 = 0 then (fastexpt (b*b) (n/2))
else b*(fastexpt b (n-1));;

(* 6. binarize *)

let rec binarize : int -> int list
= fun n -> 
  if n <= 1 then n :: []
  else (binarize (n/2)) @ [n mod 2] ;;

(* 7. iter *)

let comp f g x = f (g x);;

let rec iter : int * (int -> int) -> (int -> int)
= fun (n, f) -> 
  if n = 0 then fun x -> x
  else if n = 1 then f
  else comp f (iter (n-1, f));;

(* 8. nat *)

type nat = ZERO | SUCC of nat;;

let rec num n =
  match n with
    | ZERO -> 0
    | SUCC n -> num n + 1;;

let rec return n =
  match n with
    | 0 -> ZERO
    | n -> SUCC (return (n-1));;

let natadd : nat -> nat -> nat
= fun n1 n2 -> return ((num n1) + (num n2));;

let natmul : nat -> nat -> nat
= fun n1 n2 -> return ((num n1) * (num n2));;

(* 9. mem *)

type btree =
	| Empty
	| Node of int * btree * btree

let rec mem : int -> btree -> bool
= fun n t ->
  match t with
    | Empty -> false
    | Node (num, left, right) -> 
      if n = num then true
      else if mem n left = true then true
      else if mem n right = true then true
      else false;;

(* 10. eval *)

type formula = 
  | True
  | False
  | Not of formula
  | AndAlso of formula * formula
  | OrElse of formula * formula
  | Imply of formula * formula
  | Equal of exp * exp

and exp = 
  | Num of int
  | Plus of exp * exp
  | Minus of exp * exp;;

let rec evalexp exp =
  match exp with
    | Num n -> n
    | Plus (e1, e2) -> (evalexp e1) + (evalexp e2)
    | Minus (e1, e2) -> (evalexp e1) - (evalexp e2);;

let rec eval : formula -> bool
= fun f -> 
  match f with
    | True -> true
    | False -> false
    | Not f -> not (eval f)
    | AndAlso (f1, f2) -> (eval f1) && (eval f2)
    | OrElse (f1, f2) -> (eval f1) || (eval f2)
    | Imply (f1, f2) -> if (eval f1) = false then true 
    else if (eval f1) && (eval f2) = true then true else false
    | Equal (e1, e2) -> if (evalexp e1) = (evalexp e2) then true else false;;

(* 11. max_min *)

let rec max : int list -> int
= fun lst -> 
  match lst with
    | [] -> 0
    | [a] -> a
    | a::b::tl -> 
      if a > b then max (a::tl)
      else max (b::tl);;

let rec min : int list -> int
= fun lst -> 
  match lst with
    | [] -> 0
    | [a] -> a
    | a::b::tl -> 
      if a < b then min (a::tl)
      else min (b::tl);;

(* 12. drop *)

let rec drop : ('a -> bool) -> 'a list -> 'a list
= fun f lst ->
  match lst with
    | [] -> []
    | hd::tl ->
      if f hd = true then drop f tl else lst;;