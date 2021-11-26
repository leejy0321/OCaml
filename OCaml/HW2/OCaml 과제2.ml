(* 1. sigma *)

let rec sigma : (int -> int) -> int -> int -> int
= fun f a b -> if a < b then (f a) + (sigma f (a+1) b)
else if a = b then (f a) else 0;;

(* 2. forall *)

let rec forall : ('a -> bool) -> 'a list -> bool
= fun f lst -> match lst with
  | [] -> true
  | hd::tl -> if f hd then forall f tl else false;;

(* 3. double *)

let comp f g x = f (g x);;
let double : ('a -> 'a) -> 'a -> 'a
= fun f -> comp f f;;

(* 4. app *)

let rec exist : 'a list -> 'a -> bool
= fun lst a -> match lst with
  | [] -> false
  | hd::tl -> if a = hd then true else exist tl a;;

let rec drop : 'a list -> 'a -> 'a list
= fun lst a ->
  match lst with
    | [] -> []
    | hd::tl -> if hd = a then drop tl a else hd::(drop tl a);;

let rec uniq : 'a list -> 'a list
= fun lst -> match lst with
  | [] -> []
  | hd::tl -> if exist tl hd then hd::(uniq (drop tl hd)) else hd::(uniq tl);;

let rec app : 'a list -> 'a list -> 'a list
= fun l1 l2 -> match l1 with
  | [] -> uniq l2
  | hd::tl -> if exist l2 hd then app tl l2 else app tl (l2@[hd]);;

(* 5. uniq *)

let rec exist : 'a list -> 'a -> bool
= fun lst a -> match lst with
  | [] -> false
  | hd::tl -> if a = hd then true else exist tl a;;

let rec drop : 'a list -> 'a -> 'a list
= fun lst a ->
  match lst with
    | [] -> []
    | hd::tl -> if hd = a then drop tl a else hd::(drop tl a);;

let rec uniq : 'a list -> 'a list
= fun lst -> match lst with
  | [] -> []
  | hd::tl -> if exist tl hd then hd::(uniq (drop tl hd)) else hd::(uniq tl);;

(* 6. reduce *)

exception Error;;
let rec reduce : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
= fun f l1 l2 accu -> match l1, l2 with
  | [], [] -> accu
  | l1, [] -> raise Error
  | [], l2 -> raise Error
  | h1::t1, h2::t2 -> reduce f t1 t2 (f h1 h2 accu);;

(* 7. zipper *)

let rec zipper : int list * int list -> int list
= fun (l1, l2) -> match (l1, l2) with
  | ([], []) -> []
  | (l1, []) -> l1
  | ([], l2) -> l2
  | (h1::t1, h2::t2) -> h1::h2::(zipper (t1, t2));;

(* 8. mirror *)

type btree = 
  | Leaf of int
  | Left of btree
  | Right of btree
  | LeftRight of btree * btree

let rec mirror : btree -> btree
= fun tree -> match tree with
  | Leaf _ -> tree
  | Left tr -> Right (mirror tr)
  | Right tr -> Left (mirror tr)
  | LeftRight (l, r) -> LeftRight (mirror r, mirror l);;

(* 9. bmul *)

exception Error;;
type digit = ZERO | ONE
type bin = digit list

let num d = match d with
  | ZERO -> 0
  | ONE -> 1;;

let return n = match n with
  | 0 -> ZERO
  | 1 -> ONE
  | _ -> raise Error;;

let rec binarize : int -> bin
= fun n -> 
  if n <= 1 then (return n)::[]
  else (binarize (n/2)) @ [return (n mod 2)];;

let rec reverse lst = match lst with
  | [] -> []
  | hd::tl -> (reverse tl)@[hd];;

let rec binint : bin -> int
= fun lst -> match lst with
  | [] -> 0
  | hd::tl -> if hd = ONE then 1 + 2*(binint tl) else 2*(binint tl);;

let bmul : bin -> bin -> bin
= fun a b -> binarize ((binint (reverse a))*(binint (reverse b)));;

(* 10. diff *)

type aexp =
  | Const of int
  | Var of string
  | Power of string * int
  | Times of aexp list
  | Sum of aexp list

let rec diff : aexp * string -> aexp
= fun (exp, x) -> match exp with
  | Const _ -> Const 0
  | Var s -> if s = x then Const 1 else Const 0
  | Power (s, n) -> if s = x then (match n with
    | 0 -> Const 0
    | 1 -> Const 1
    | n -> Times [Const n; Power (s, (n-1))]) else Const 0
  | Times lst -> (match lst with
    | [] -> Const 1
    | hd::tl -> (match hd with
      | Const n -> Times [Const n; diff (Times tl, x)]
      | Var s -> if s = x then diff (Times tl, x) else Times [Const 1; diff (Times tl, x)]
      | Power (s, n) -> if s = x then Times [diff (hd, x); diff (Times tl, x)] 
      else Times [hd; diff (Times tl, x)]
      | Times lst -> Times [diff (hd, x); diff (Times tl, x)]
      | Sum lst -> Times [diff (hd, x); diff (Times tl, x)]))
  | Sum lst -> (match lst with
    | [] -> Const 0
    | hd::tl -> (match hd with
      | Const _ -> Const 0
      | Var s -> if s = x then Sum [Const 1; diff (Sum tl, x)] else Sum [Const 0; diff (Sum tl, x)]
      | Power (s, n) -> if s = x then Sum [diff (hd, x); diff (Sum tl, x)]
      else Sum [Const 0; diff (Sum tl, x)]
      | Times lst -> Sum [diff (hd, x); diff (Sum tl, x)]
      | Sum lst -> Sum [diff (hd, x); diff (Sum tl, x)]));;

(* Feedback *)

type aexp =
  | Const of int
  | Var of string
  | Power of string * int
  | Times of aexp list
  | Sum of aexp list

let rec diff : aexp * string -> aexp
= fun (exp, x) ->
  match exp with
  | Const n -> Const 0
  | Var y -> if x = y then Const 1 else Const 0
  | Power (y, n) -> if x = y then Times [Const n; Power (y, n - 1)] else Const 0
  | Times [] -> Const 0
  | Times (hd::tl) -> Sum [Times (diff (hd, x)::tl); Times [hd; diff (Times tl, x)]] 
  | Sum [] -> Const 0
  | Sum (hd::tl) -> Sum [diff (hd, x); diff (Sum tl, x)]

(* 11. calculator *)

type exp =
  | X
  | INT of int
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | SIGMA of exp * exp * exp

exception Error

let rec xlist : exp -> exp list
= fun e -> match e with
  | X -> e::[]
  | INT _ -> []
  | ADD (a, b) -> (xlist a) @ (xlist b)
  | SUB (a, b) -> (xlist a) @ (xlist b)
  | MUL (a, b) -> (xlist a) @ (xlist b)
  | DIV (a, b) -> (xlist a) @ (xlist b)
  | SIGMA (a, b, c) -> xlist c;;

let rec xexist : exp list -> bool
= fun lst -> match lst with
  | [] -> false
  | hd::tl -> if hd = X then true else xexist tl;;

let rec expint : exp -> int
= fun e -> match e with
  | X -> raise Error
  | INT n -> n
  | ADD (a, b) -> (expint a) + (expint b)
  | SUB (a, b) -> (expint a) - (expint b)
  | MUL (a, b) -> (expint a) * (expint b)
  | DIV (a, b) -> if (expint b) = 0 then raise Error else (expint a) / (expint b)
  | SIGMA (a, b, c) -> if xexist (xlist c) then raise Error else expint (MUL (ADD (SUB (b, a), INT 1), c));;

let intexp : int -> exp
= fun n -> INT n;;

let rec xcal : exp -> exp -> exp
= fun e1 e2 -> match e1 with
  | X -> e2
  | INT _ -> e1
  | ADD (a, b) -> ADD ((xcal a e2), (xcal b e2))
  | SUB (a, b) -> SUB ((xcal a e2), (xcal b e2))
  | MUL (a, b) -> MUL ((xcal a e2), (xcal b e2))
  | DIV (a, b) -> DIV ((xcal a e2), (xcal b e2))
  | SIGMA (a, b, c) -> if xexist (xlist c) 
  then (if expint a = expint b then xcal c a
  else if expint a < expint b then ADD ((xcal c a), SIGMA (intexp (expint a + 1), b, c))
  else INT 0)
  else MUL (ADD (SUB (b, a), INT 1), c);;

let rec calculator : exp -> int
= fun exp -> match exp with
  | X -> 0
  | INT n -> n
  | ADD (a, b) -> (calculator a) + (calculator b)
  | SUB (a, b) -> (calculator a) - (calculator b)
  | MUL (a, b) -> (calculator a) * (calculator b)
  | DIV (a, b) -> if (calculator b) = 0 then raise Error else (calculator a) / (calculator b)
  | SIGMA (a, b, c) -> if (calculator a) = (calculator b)
  then (match c with
    | X -> calculator b
    | _ -> if xexist (xlist c) then calculator (xcal c b) else calculator c)
  else if (calculator a) < (calculator b) then (match c with
    | X -> calculator (ADD (a, SIGMA (ADD (a, INT 1), b, c)))
    | INT n -> calculator (MUL (ADD (SUB (b, a), INT 1), c))
    | _ -> calculator (ADD ((xcal c a), SIGMA (intexp ((expint a) + 1), b, c))))
  else 0;;

(* Feedback *)

type exp =
  | X
  | INT of int
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | SIGMA of exp * exp * exp

let rec calculator_aux : exp -> int option -> int
= fun exp x ->
  match exp with
  | X ->
    begin
      match x with
      | Some x -> x
      | None -> raise (Failure "Invalid input")
    end
  | INT n -> n
  | ADD (e1, e2) -> calculator_aux e1 x + calculator_aux e2 x
  | SUB (e1, e2) -> calculator_aux e1 x - calculator_aux e2 x
  | MUL (e1, e2) -> calculator_aux e1 x * calculator_aux e2 x
  | DIV (e1, e2) -> calculator_aux e1 x / calculator_aux e2 x
  | SIGMA (a, b, f) ->
    begin
      let a = calculator_aux a x in
      let b = calculator_aux b x in
      if a > b then
        0
      else
        calculator_aux f (Some a) + calculator_aux (SIGMA ((INT (a + 1)), INT b, f)) x
    end


let calculator : exp -> int
= fun exp -> calculator_aux exp None

(* 12. check *)

type exp = 
  | V of var
  | P of var * exp
  | C of exp * exp
and var = string

let rec exist : 'a list -> 'a -> bool
= fun lst a -> match lst with
  | [] -> false
  | hd::tl -> if a = hd then true else exist tl a;;

let rec drop : 'a list -> 'a -> 'a list
= fun lst a ->
  match lst with
    | [] -> []
    | hd::tl -> if hd = a then drop tl a else hd::(drop tl a);;

let rec uniq : 'a list -> 'a list
= fun lst -> match lst with
  | [] -> []
  | hd::tl -> if exist tl hd then hd::(uniq (drop tl hd)) else hd::(uniq tl);;

let rec envlist e l = match e with
  | P (x, e1) -> if exist l x then envlist e1 l else envlist e1 (x::l)
  | V x -> l
  | C (e1, e2) -> uniq ((envlist e1 l) @ (envlist e2 l));;

let rec varlist v l = match v with
  | V x -> x::l
  | P (_, e) -> varlist e l
  | C (e1, e2) -> uniq ((varlist e1 l) @ (varlist e2 l));;

let rec sublist var env = match env with
  | [] -> var
  | hd::tl -> sublist (drop var hd) tl;;

let rec check : exp -> bool
= fun exp -> if sublist (varlist exp []) (envlist exp []) = [] then true else false;;

(* Feedback *)

type exp =
  | V of var
  | P of var * exp
  | C of exp * exp
and var = string

let rec exists : var -> var list -> bool
= fun var vars ->
  match vars with
  | [] -> false
  | hd::tl -> if hd = var then true else exists var tl

let rec check_aux : exp -> var list -> bool
= fun exp vars ->
  match exp with
  | V v -> exists v vars
  | P (v, exp) -> check_aux exp (v::vars)
  | C (e1, e2) -> check_aux e1 vars && check_aux e2 vars

let check : exp -> bool
= fun exp -> check_aux exp []
