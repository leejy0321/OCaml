type exp =
  | NUM of int | TRUE | FALSE | UNIT
  | VAR of id
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | SEQ of exp * exp                 (* sequence *)
  | IF of exp * exp * exp            (* if-then-else *)
  | WHILE of exp * exp               (* while loop *)
  | LETV of id * exp * exp           (* variable binding *)
  | LETF of id * id list * exp * exp (* procedure binding *)
  | CALLV of id * exp list           (* call by value *)
  | CALLR of id * id list            (* call by referenece *)
  | RECORD of (id * exp) list        (* record construction *)
  | FIELD of exp * id                (* access record field *)
  | ASSIGN of id * exp               (* assgin to variable *)
  | ASSIGNF of exp * id * exp        (* assign to record field *)
  | WRITE of exp
and id = string

type loc = int
type value =
| Num of int
| Bool of bool
| Unit
| Record of record 
and record = (id * loc) list
type memory = (loc * value) list
type env = binding list
and binding = LocBind of id * loc | ProcBind of id * proc
and proc = id list * exp * env

(********************************)
(*     Handling environment     *)
(********************************)

let rec lookup_loc_env : id -> env -> loc
= fun x env ->
  match env with
  | [] -> raise(Failure ("Variable "^x^" is not included in environment"))
  | hd::tl ->
    begin match hd with
    | LocBind (id,l) -> if(x=id) then l else lookup_loc_env x tl
    | ProcBind _ -> lookup_loc_env x tl
    end

let rec lookup_proc_env : id -> env -> proc
= fun x env ->
  match env with
  | [] -> raise(Failure ("Variable "^x^" is not included in environment"))
  | hd::tl ->
    begin match hd with
    | LocBind _ -> lookup_proc_env x tl
    | ProcBind (id,binding) -> if (x=id) then binding else lookup_proc_env x tl
    end

let extend_env : binding -> env -> env
= fun e env -> e::env

let empty_env = []


(***************************)
(*     Handling memory     *)
(***************************)

let rec lookup_mem : loc -> memory -> value
= fun l mem ->
  match mem with
  | [] -> raise(Failure ("location "^(string_of_int l)^" is not included in memory"))
  | (loc,v)::tl -> if(l=loc) then v else lookup_mem l tl

let extend_mem : (loc * value) -> memory -> memory
= fun (l,v) mem -> (l,v)::mem

let empty_mem = []

(***************************)
(*     Handling record     *)
(***************************)

let rec lookup_record : id -> record -> loc
= fun id record -> 
  match record with
    | [] -> raise(Failure ("field "^ id ^" is not included in record"))
    | (x,l)::tl -> if(id=x) then l else lookup_record id tl


let extend_record : (id * loc) -> record -> record
= fun (x,l) record -> (x,l)::record

let empty_record = []

(***************************)

let counter = ref 0
let new_location () = counter:=!counter+1;!counter

exception NotImplemented
exception UndefinedSemantics

let rec list_fold2 : ('a -> 'b -> 'c -> 'c)-> 'a list -> 'b list -> 'c -> 'c
= fun func l1 l2 acc ->
  match (l1,l2) with
  | ([],[]) -> acc
  | (hd1::tl1,hd2::tl2) -> list_fold2 func tl1 tl2 (func hd1 hd2 acc)
  | _ -> raise (Failure "two lists have different length")

let rec list_fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
= fun func l acc ->
  match l with
  | [] -> acc
  | hd::tl -> list_fold func tl (func hd acc)

let value2str : value -> string
= fun v ->
  match v with
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Unit -> "unit"
  | Record _ -> "record" 

let rec eval_aop : env -> memory -> exp -> exp -> (int -> int -> int) -> (value * memory)
= fun env mem e1 e2 op ->
  let (v1,mem1) = eval env mem e1 in
  let (v2,mem2) = eval env mem1 e2 in
  match (v1,v2) with
  | (Num n1, Num n2) -> (Num (op n1 n2), mem2)
  | _ -> raise (Failure "arithmetic operation type error")

and eval : env -> memory -> exp -> (value * memory) 
=fun env mem e -> 
  match e with
  | TRUE -> (Bool true, mem)
  | FALSE -> (Bool false, mem)
  | NUM n -> (Num n, mem)
  | UNIT -> (Unit, mem)
  | VAR x -> ((lookup_mem (lookup_loc_env x env) mem), mem)
  | ADD (e1, e2) -> eval_aop env mem e1 e2 ( + )
  | SUB (e1, e2) -> eval_aop env mem e1 e2 ( - )
  | MUL (e1, e2) -> eval_aop env mem e1 e2 ( * )
  | DIV (e1, e2) -> eval_aop env mem e1 e2 ( / )
  | EQUAL (e1, e2) -> 
    let (v1, mem1) = eval env mem e1 in
    let (v2, mem2) = eval env mem1 e2 in
    if v1 = v2 then 
    begin match v1 with
      | Num _ -> (Bool true, mem2)
      | Bool _ -> (Bool true, mem2)
      | Unit -> (Bool true, mem2)
      | _ -> (Bool false, mem2)
    end
    else (Bool false, mem2)
  | LESS (e1, e2) ->
    let (n1, mem1) = eval env mem e1 in
    let (n2, mem2) = eval env mem1 e2 in
    if n1 < n2 then (Bool true, mem2) else (Bool false, mem2)
  | NOT e ->
    let (b, mem1) = eval env mem e in
    begin match b with
      | Bool true -> (Bool false, mem1)
      | Bool false -> (Bool true, mem1)
      | _ -> raise UndefinedSemantics
    end
  | SEQ (e1, e2) ->
    let (v1, mem1) = eval env mem e1 in
    let (v2, mem2) = eval env mem1 e2 in
    (v2, mem2)
  | IF (e, e1, e2) ->
    let (b, mem1) = eval env mem e in
    begin match b with
      | Bool true -> let (v, mem2) = eval env mem1 e1 in (v, mem2)
      | Bool false -> let (v, mem2) = eval env mem1 e2 in (v, mem2)
      | _ -> raise UndefinedSemantics
    end
  | WHILE (e1, e2) ->
    let (b, memp) = eval env mem e1 in
    begin match b with
      | Bool false -> (Unit, memp)
      | Bool true -> let (v1, mem1) = eval env memp e2 in
      let (v2, mem2) = eval env mem1 (WHILE (e1, e2)) in (v2, mem2)
      | _ -> raise UndefinedSemantics
    end
  | LETV (x, e1, e2) ->
    let (v, mem1) = eval env mem e1 in
    let l = new_location () in
    let (v1, mem2) = eval (extend_env (LocBind (x, l)) env) (extend_mem (l, v) mem1) e2 in
    (v1, mem2)
  | LETF (f, lst, e1, e2) ->
    let (v, mem1) = eval (extend_env (ProcBind (f, (lst, e1, env))) env) mem e2 in
    (v, mem1)
  | CALLV (f, lst) ->
    begin match lst with
      | [] -> raise UndefinedSemantics
      | hd::tl ->
        let (v1, mem1) = eval env mem hd in
        let (xlist, exp1, env1) = lookup_proc_env f env in
        let l1 = new_location () in
        let x1 =
          begin match xlist with
            | [] -> raise UndefinedSemantics
            | head::tail -> head
          end
        in
        let modxlist =
          begin match xlist with
            | [] -> raise UndefinedSemantics
            | head::tail -> tail @ [head]
          end
        in
        let env2 = extend_env (LocBind (x1, l1)) env1 in
        let envn = extend_env (ProcBind (f, (modxlist, exp1, env2))) env2 in
        let memn = extend_mem (l1, v1) mem1 in
        begin match tl with
          | [] -> eval envn memn exp1
          | hd2::tl2 -> eval envn memn (CALLV (f, tl))
        end
    end
  | CALLR (f, lst) ->
    begin match lst with
      | [] -> raise UndefinedSemantics
      | hd::tl ->
        let (xlist, exp1, envp) = lookup_proc_env f env in
        let x1 =
          begin match xlist with
            | [] -> raise UndefinedSemantics
            | head::tail -> head
          end
        in
        let y1 = hd in
        let env1 = extend_env (LocBind (x1, lookup_loc_env y1 env)) env in
        let modxlist =
          begin match xlist with
            | [] -> raise UndefinedSemantics
            | head2::tail2 -> tail2 @ [head2]
          end
        in
        let envn = extend_env (ProcBind (f, (modxlist, exp1, env1))) env1 in
        begin match tl with
          | [] -> eval envn mem exp1
          | hd2::tl2 -> eval envn mem (CALLR (f, tl))
        end
    end
  | RECORD lst ->
    begin match lst with
      | [] -> (Unit, mem)
      | hd::tl ->
        let (x1, e1) = hd in
        let (v1, mem1) = eval env mem e1 in
        let l1 = new_location () in
        let recordn, memn =
          let record1 = extend_record (x1, l1) empty_record in
          let mem1 = extend_mem (l1, v1) mem1 in
          let (Record templist, tempmem) = 
            begin match tl with
              | [] -> (Record record1, mem1)
              | head::tail -> let (Record templ, tempm) = eval env mem1 (RECORD tl) in
              (Record (record1 @ templ), tempm)
            end
          in
          let recordn = templist in
          let memn = tempmem in
          recordn, memn
        in (Record recordn, memn)
    end
  | FIELD (e, x) ->
    let (Record r, mem1) = eval env mem e in
    (lookup_mem (lookup_record x r) mem1, mem1)
  | ASSIGN (x, e) ->
    let (v, mem1) = eval env mem e in
    (v, (extend_mem ((lookup_loc_env x env), v) mem1))
  | ASSIGNF (e1, x, e2) ->
    let (Record r, mem1) = eval env mem e1 in
    let (v, mem2) = eval env mem1 e2 in
    (v, extend_mem ((lookup_record x r), v) mem2)
  | WRITE e -> 
    let (v1,mem1) = eval env mem e in
    let _ = print_endline(value2str v1) in
    (v1,mem1)
  | _ -> raise NotImplemented

let runb : exp -> value 
=fun exp -> let (v, _) = eval empty_env empty_mem exp in v;;


(* Feedback *)


type exp =
  | NUM of int | TRUE | FALSE | UNIT
  | VAR of id
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | SEQ of exp * exp                 (* sequence *)
  | IF of exp * exp * exp            (* if-then-else *)
  | WHILE of exp * exp               (* while loop *)
  | LETV of id * exp * exp           (* variable binding *)
  | LETF of id * id list * exp * exp (* procedure binding *)
  | CALLV of id * exp list           (* call by value *)
  | CALLR of id * id list            (* call by referenece *)
  | RECORD of (id * exp) list        (* record construction *)
  | FIELD of exp * id                (* access record field *)
  | ASSIGN of id * exp               (* assgin to variable *)
  | ASSIGNF of exp * id * exp        (* assign to record field *)
  | WRITE of exp
and id = string

type loc = int
type value =
| Num of int
| Bool of bool
| Unit
| Record of record 
and record = (id * loc) list
type memory = (loc * value) list
type env = binding list
and binding = LocBind of id * loc | ProcBind of id * proc
and proc = id list * exp * env

(********************************)
(*     Handling environment     *)
(********************************)

let rec lookup_loc_env : id -> env -> loc
= fun x env ->
  match env with
  | [] -> raise(Failure ("Variable "^x^" is not included in environment"))
  | hd::tl ->
    begin match hd with
    | LocBind (id,l) -> if(x=id) then l else lookup_loc_env x tl
    | ProcBind _ -> lookup_loc_env x tl
    end

let rec lookup_proc_env : id -> env -> proc
= fun x env ->
  match env with
  | [] -> raise(Failure ("Variable "^x^" is not included in environment"))
  | hd::tl ->
    begin match hd with
    | LocBind _ -> lookup_proc_env x tl
    | ProcBind (id,binding) -> if (x=id) then binding else lookup_proc_env x tl
    end

let extend_env : binding -> env -> env
= fun e env -> e::env

let empty_env = []


(***************************)
(*     Handling memory     *)
(***************************)

let rec lookup_mem : loc -> memory -> value
= fun l mem ->
  match mem with
  | [] -> raise(Failure ("location "^(string_of_int l)^" is not included in memory"))
  | (loc,v)::tl -> if(l=loc) then v else lookup_mem l tl

let extend_mem : (loc * value) -> memory -> memory
= fun (l,v) mem -> (l,v)::mem

let empty_mem = []

(***************************)
(*     Handling record     *)
(***************************)

let rec lookup_record : id -> record -> loc
= fun id record -> 
  match record with
    | [] -> raise(Failure ("field "^ id ^" is not included in record"))
    | (x,l)::tl -> if(id=x) then l else lookup_record id tl


let extend_record : (id * loc) -> record -> record
= fun (x,l) record -> (x,l)::record

let empty_record = []

(***************************)

let counter = ref 0
let new_location () = counter:=!counter+1;!counter

exception NotImplemented
exception UndefinedSemantics

let rec list_fold2 : ('a -> 'b -> 'c -> 'c)-> 'a list -> 'b list -> 'c -> 'c
= fun func l1 l2 acc ->
  match (l1,l2) with
  | ([],[]) -> acc
  | (hd1::tl1,hd2::tl2) -> list_fold2 func tl1 tl2 (func hd1 hd2 acc)
  | _ -> raise (Failure "two lists have different length")

let rec list_fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
= fun func l acc ->
  match l with
  | [] -> acc
  | hd::tl -> list_fold func tl (func hd acc)

let value2str : value -> string
= fun v ->
  match v with
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Unit -> "unit"
  | Record _ -> "record"

let rec map : ('a -> 'b) -> 'a list -> 'b list
= fun f l ->
  match l with
  | [] -> []
  | hd::tl -> (f hd)::(map f tl)

let rec eval_aop : env -> memory -> exp -> exp -> (int -> int -> int) -> (value * memory)
= fun env mem e1 e2 op ->
  let (v1,mem1) = eval env mem e1 in
  let (v2,mem2) = eval env mem1 e2 in
  match (v1,v2) with
  | (Num n1, Num n2) -> (Num (op n1 n2), mem2)
  | _ -> raise (Failure "arithmetic operation type error")

and eval : env -> memory -> exp -> (value * memory) 
=fun env mem e -> 
  match e with
  | WRITE e -> 
    let (v1,mem1) = eval env mem e in
    let _ = print_endline(value2str v1) in
    (v1,mem1)
  | NUM n -> (Num n, mem)
  | TRUE -> (Bool true, mem)
  | FALSE -> (Bool false, mem)
  | UNIT -> (Unit, mem)
  | VAR x -> let l = lookup_loc_env x env in (lookup_mem l mem, mem)
  | ADD (e1, e2) -> eval_aop env mem e1 e2 (+)
  | SUB (e1, e2) -> eval_aop env mem e1 e2 (-)
  | MUL (e1, e2) -> eval_aop env mem e1 e2 ( * )
  | DIV (e1, e2) -> eval_aop env mem e1 e2 (/)
  | EQUAL (e1, e2) ->
    begin
      let v1, mem = eval env mem e1 in
      let v2, mem = eval env mem e2 in
      match v1, v2 with
      | Num n1, Num n2 -> Bool (n1 = n2), mem
      | Bool b1, Bool b2 -> Bool (b1 = b2), mem
      | Unit, Unit -> Bool true, mem
      | _ -> Bool false, mem
    end
  | LESS (e1, e2) ->
    begin
      let n1, mem = eval env mem e1 in
      let n2, mem = eval env mem e2 in
      match n1, n2 with
      | Num n1, Num n2 -> Bool (n1 < n2), mem
      | _ -> raise UndefinedSemantics
    end
  | NOT e ->
    begin
      let b, mem = eval env mem e in
      match b with
      | Bool b -> Bool (not b), mem
      | _ -> raise UndefinedSemantics
    end
  | SEQ (e1, e2) -> let _, mem = eval env mem e1 in eval env mem e2
  | IF (cond, e1, e2) ->
    begin
      let cond, mem = eval env mem cond in
      match cond with
      | Bool b -> eval env mem (if b then e1 else e2)
      | _ -> raise UndefinedSemantics
    end
  | WHILE (cond, body) ->
    begin
      let cond, mem = eval env mem cond in
      match cond with
      | Bool true -> let _, mem = eval env mem body in eval env mem e
      | Bool false -> (Unit, mem)
      | _ -> raise UndefinedSemantics
    end
  | LETV (x, e1, e2) ->
    let v, mem = eval env mem e1 in
    let l = new_location () in
    let env = extend_env (LocBind (x, l)) env in
    let mem = extend_mem (l, v) mem in
    eval env mem e2
  | LETF (f, xs, body, e) ->
    let proc = (xs, body, env) in
    let env = extend_env (ProcBind (f, proc)) env in
    eval env mem e
  | CALLV (f, args) ->
    let xs, body, env1 = lookup_proc_env f env in
    let locs = map (fun _ -> new_location ()) xs in
    let args, mem = list_fold (fun arg (accu, mem) -> let arg, mem = eval env mem arg in (accu@[arg], mem)) args ([], mem) in
    let env = list_fold2 (fun x l env -> extend_env (LocBind (x, l)) env) xs locs env1 in
    let env = extend_env (ProcBind (f, (xs, body, env1))) env in
    let mem = list_fold2 (fun l v mem -> extend_mem (l, v) mem) locs args mem in
    eval env mem body
  | CALLR (f, args) ->
    let xs, body, env1 = lookup_proc_env f env in
    let locs = map (fun arg -> lookup_loc_env arg env) args in
    let env = list_fold2 (fun x l env -> extend_env (LocBind (x, l)) env) xs locs env1 in
    let env = extend_env (ProcBind (f, (xs, body, env1))) env in
    eval env mem body
  | RECORD record ->
    begin
      match record with
      | [] -> Unit, mem
      | _ ->
        let record, mem = list_fold (fun (x, e) (record, mem) ->
          let v, mem = eval env mem e in
          (record@[(x, v)], mem)) record ([], mem) in
        let record, mem = list_fold (fun (x, v) (record, mem) ->
          let l = new_location () in
          let mem = extend_mem (l, v) mem in
          let record = extend_record (x, l) record in
          (record, mem)) record (empty_mem, mem) in
        (Record record, mem)
    end
  | FIELD (r, x) ->
    begin
      let r, mem = eval env mem r in
      match r with
      | Record r ->
        let l = lookup_record x r in
        (lookup_mem l mem, mem)
      | _ -> raise UndefinedSemantics
    end
  | ASSIGN (x, e) ->
    let v, mem = eval env mem e in
    let l = lookup_loc_env x env in
    let mem = extend_mem (l, v) mem in
    v, mem
  | ASSIGNF (r, x, e) ->
    begin
      let r, mem = eval env mem r in
      match r with
      | Record r ->
        let l = lookup_record x r in
        let v, mem = eval env mem e in
        let mem = extend_mem (l, v) mem in
        (v, mem)
      | _ -> raise UndefinedSemantics
    end


let runb : exp -> value 
=fun exp -> let (v, _) = eval empty_env empty_mem exp in v;;
