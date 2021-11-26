type program = exp
and exp = 
  | UNIT
  | TRUE
  | FALSE
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | NIL
  | CONS of exp * exp      
  | APPEND of exp * exp
  | HEAD of exp
  | TAIL of exp
  | ISNIL of exp
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | LETMREC of (var * var * exp) * (var * var * exp) * exp
  | PROC of var * exp
  | CALL of exp * exp
  | PRINT of exp
  | SEQ of exp * exp 
and var = string

type value = 
  | Unit
  | Int of int
  | Bool of bool
  | List of value list
  | Procedure of var * exp * env 
  | RecProcedure of var * var * exp * env
  | MRecProcedure of (var * var * exp) * (var * var * exp) * env
and env = (var * value) list

let rec fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
= fun f accu lst ->
  match lst with
  | [] -> accu
  | hd::tl -> fold_left f (f accu hd) tl

let rec map : ('a -> 'b) -> 'a list -> 'b list
= fun f lst ->
  match lst with
  | [] -> []
  | hd::tl -> (f hd)::(map f tl)

let rec string_of_value v = 
  match v with
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | List lst -> "[" ^ fold_left (fun s x -> s ^ ", " ^ x) "" (map string_of_value lst) ^ "]"
  | _ -> "(functional value)"

exception UndefinedSemantics

let empty_env = []
let extend_env (x,v) e = (x,v)::e
let rec lookup_env x e = 
  match e with
  | [] -> raise (Failure ("variable " ^ x ^ " is not bound in env")) 
  | (y,v)::tl -> if x = y then v else lookup_env x tl

let int_of_value : value -> int
= fun v -> match v with
  | Int n -> n
  | _ -> raise (Failure ("It is not integer value"))

let rec eval : exp -> env -> value
= fun exp env ->
  match exp with
  | PRINT e -> (print_endline (string_of_value (eval e env)); Unit)
  | UNIT -> Unit
  | TRUE -> Bool true
  | FALSE -> Bool false
  | CONST n -> Int n
  | VAR v -> lookup_env v env
  | ADD (e1, e2) -> Int ((int_of_value (eval e1 env)) + (int_of_value (eval e2 env)))
  | SUB (e1, e2) -> Int ((int_of_value (eval e1 env)) - (int_of_value (eval e2 env)))
  | MUL (e1, e2) -> Int ((int_of_value (eval e1 env)) * (int_of_value (eval e2 env)))
  | DIV (e1, e2) -> if (int_of_value (eval e2 env)) = 0 then raise (Failure ("Unable to divide by zero"))
  else Int ((int_of_value (eval e1 env)) / (int_of_value (eval e2 env)))
  | EQUAL (e1, e2) -> (match (eval e1 env), (eval e2 env) with
    | (Int n1), (Int n2) -> if n1 = n2 then Bool true else Bool false
    | (Bool b1), (Bool b2) -> if b1 = b2 then Bool true else Bool false
    | _, _ -> raise UndefinedSemantics)
  | LESS (e1, e2) -> (match (eval e1 env), (eval e2 env) with
    | (Int n1), (Int n2) -> if n1 < n2 then Bool true else Bool false
    | _, _ -> raise UndefinedSemantics)
  | NOT e -> (match (eval e env) with
    | Bool true -> Bool false
    | Bool false -> Bool true
    | _ -> raise UndefinedSemantics)
  | NIL -> List []
  | CONS (e1, e2) -> (match (eval e2 env) with
    | List lst -> List ((eval e1 env)::lst)
    | _ -> raise UndefinedSemantics)
  | APPEND (e1, e2) -> (match (eval e1 env), (eval e2 env) with
    | List l1, List l2 -> List (l1 @ l2)
    | _ -> raise UndefinedSemantics)
  | HEAD e -> (match (eval e env) with
    | List lst -> (match lst with
      | [] -> Unit
      | hd::tl -> hd)
    | _ -> raise UndefinedSemantics)
  | TAIL e -> (match (eval e env) with
    | List lst -> (match lst with
      | [] -> List []
      | hd::tl -> List tl)
    | _ -> raise UndefinedSemantics)
  | ISNIL e -> (match (eval e env) with
    | List lst -> (match lst with
      | [] -> Bool true
      | hd::tl -> Bool false)
    | _ -> raise UndefinedSemantics)
  | IF (e1, e2, e3) -> (match (eval e1 env) with
    | Bool true -> eval e2 env
    | Bool false -> eval e3 env
    | _ -> raise UndefinedSemantics)
  | LET (x, e1, e2) -> (eval e2 (extend_env (x, (eval e1 env)) env))
  | LETREC (f, x, e1, e2) -> (eval e2 (extend_env (f, (RecProcedure (f, x, e1, env))) env))
  | LETMREC ((f, x, e1), (g, y, e2), e3) ->
    (eval e3 (extend_env (f, MRecProcedure ((f, x, e1), (g, y, e2), env)) 
    (extend_env (g, MRecProcedure ((g, y, e2), (f, x, e1), env)) env)))
  | PROC (v, e) -> Procedure (v, e, env)
  | CALL (e1, e2) -> (match (eval e1 env) with
    | Procedure (x, e, env1) -> (eval e (extend_env (x, (eval e2 env)) env1))
    | RecProcedure (f, x, e, env1) -> 
      (eval e (extend_env (x, (eval e2 env)) (extend_env (f, RecProcedure (f, x, e, env1)) env1)))
    | MRecProcedure ((f, x, ef), (g, y, eg), env1) ->
      (eval ef (extend_env (x, (eval e2 env)) 
      (extend_env (f, MRecProcedure ((f, x, ef), (g, y, eg), env1))
      (extend_env (g, MRecProcedure ((g, y, eg), (f, x, ef), env1)) env1))))
    | _ -> raise UndefinedSemantics)
  | SEQ (e1, e2) -> ignore (eval e1 env); (eval e2 env);;

let runml : program -> value
=fun pgm -> eval pgm empty_env;;