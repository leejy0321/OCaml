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

exception TypeError

type typ = 
    TyUnit 
  | TyInt 
  | TyBool 
  | TyFun of typ * typ 
  | TyList of typ
  | TyVar of tyvar
and tyvar = string


(* You can invoke "fresh_tyvar()" to generate a fresh type variable *)
let tyvar_num = ref 0
let fresh_tyvar () = (tyvar_num := !tyvar_num + 1; (TyVar ("t" ^ string_of_int !tyvar_num)))

type tyenv = (var * typ) list
let empty_tyenv = []
let extend_tyenv (x,t) r = (x,t)::r
let rec lookup_tyenv : var -> tyenv -> typ
= fun x r ->
  match r with
    | [] -> raise TypeError
    | (var,typ)::tl -> if x = var then typ else lookup_tyenv x tl

type tyeqn = (typ * typ) list
let empty_tyeqn = []
let extend_tyeqn (t1,t2) te = (t1,t2)::te

let rec v : tyenv -> exp -> typ -> tyeqn
= fun r e t ->
  match e with
    | UNIT -> [(t, TyUnit)]
    | TRUE -> [(t, TyBool)]
    | FALSE -> [(t, TyBool)]
    | CONST n -> [(t, TyInt)]
    | VAR x -> [(t, lookup_tyenv x r)]
    | ADD (e1, e2) -> extend_tyeqn (t, TyInt) ((v r e1 TyInt) @ (v r e2 TyInt))
    | SUB (e1, e2) -> extend_tyeqn (t, TyInt) ((v r e1 TyInt) @ (v r e2 TyInt))
    | MUL (e1, e2) -> extend_tyeqn (t, TyInt) ((v r e1 TyInt) @ (v r e2 TyInt))
    | DIV (e1, e2) -> extend_tyeqn (t, TyInt) ((v r e1 TyInt) @ (v r e2 TyInt))
    | EQUAL (e1, e2) -> let a = fresh_tyvar () in
    extend_tyeqn (t, TyBool) ((v r e1 a) @ (v r e2 a))
    | LESS (e1, e2) -> extend_tyeqn (t, TyBool) ((v r e1 TyInt) @ (v r e2 TyInt))
    | NOT e -> extend_tyeqn (t, TyBool) (v r e TyBool)
    | NIL -> let a = fresh_tyvar () in [(t, TyList a)]
    | CONS (e1, e2) -> let a = fresh_tyvar () in
    extend_tyeqn (t, TyList a) ((v r e1 a) @ (v r e2 (TyList a)))
    | APPEND (e1, e2) -> let a = fresh_tyvar () in
    extend_tyeqn (t, TyList a) ((v r e1 (TyList a)) @ (v r e2 (TyList a)))
    | HEAD e -> let a = fresh_tyvar () in
    extend_tyeqn (t, a) (v r e (TyList a))
    | TAIL e -> let a = fresh_tyvar () in
    extend_tyeqn (t, (TyList a)) (v r e (TyList a))
    | ISNIL e -> let a = fresh_tyvar () in
    extend_tyeqn (t, TyBool) (v r e (TyList a))
    | IF (e1, e2, e3) -> (v r e1 TyBool) @ (v r e2 t) @ (v r e3 t)
    | LET (x, e1, e2) -> let a = fresh_tyvar () in
    (v r e1 a) @ (v (extend_tyenv (x, a) r) e2 t)
    | LETREC (f, x, e1, e2) -> 
      let a = fresh_tyvar () in
      let b = fresh_tyvar () in
      (v (extend_tyenv (x, b) (extend_tyenv (f, TyFun (b, a)) r)) e1 a) @ 
      (v (extend_tyenv (f, TyFun (b, a)) r) e2 t)
    | LETMREC ((f, x, e1), (g, y, e2), e3) ->
      let a = fresh_tyvar () in
      let b = fresh_tyvar () in
      let c = fresh_tyvar () in
      let d = fresh_tyvar () in
      (v (extend_tyenv (x, b) (extend_tyenv (f, TyFun (b, a)) (extend_tyenv (y, d) (extend_tyenv (g, TyFun (d, c)) r)))) e1 a) @ 
      (v (extend_tyenv (y, d) (extend_tyenv (g, TyFun (d, c)) (extend_tyenv (x, b) (extend_tyenv (f, TyFun (b, a)) r)))) e2 c) @ 
      (v (extend_tyenv (f, TyFun (b, a)) (extend_tyenv (g, TyFun (d, c)) r)) e3 t)
    | PROC (x, e) -> 
      let a1 = fresh_tyvar () in
      let a2 = fresh_tyvar () in
      extend_tyeqn (t, TyFun (a1, a2)) (v (extend_tyenv (x, a1) r) e a2)
    | CALL (e1, e2) -> let a = fresh_tyvar () in
    (v r e1 (TyFun (a, t))) @ (v r e2 a)
    | PRINT e -> let a = fresh_tyvar () in extend_tyenv (t, TyUnit) (v r e a)
    | SEQ (e1, e2) ->
      let a = fresh_tyvar () in
      let b = fresh_tyvar () in
      extend_tyeqn (t, b) ((v r e1 a) @ (v r e2 b))

type subst = (tyvar * typ) list
let empty_subst = []
let extend_subst (a,t) s = (a,t)::s
let rec lookup_subst : tyvar -> subst -> typ
= fun a s ->
  match s with
    | [] -> TyVar a
    | (v,t)::tl -> if a = v then t else lookup_subst a tl

let rec substitution : typ -> subst -> typ
= fun t s ->
  match t with
    | TyUnit -> TyUnit
    | TyInt -> TyInt
    | TyBool -> TyBool
    | TyVar a -> lookup_subst a s
    | TyFun (t1, t2) -> TyFun (substitution t1 s, substitution t2 s)
    | TyList t1 -> TyList (substitution t1 s)

let rec occur : typ -> typ -> bool
= fun a t ->
  match t with
    | TyUnit -> false
    | TyInt -> false
    | TyBool -> false
    | TyVar b -> if TyVar b = a then true else false
    | TyFun (t1, t2) ->
      if t1 = a then true
      else if t2 = a then true
      else if occur a t1 then true else occur a t2
    | TyList typ -> if typ = a then true else occur a typ

let rec change2 : typ -> typ -> typ -> typ
= fun t1 t2 t ->
  match t with
    | TyVar _ -> t2
    | TyFun (tf1, tf2) -> if occur t1 tf1 then TyFun (change2 t1 t2 tf1, tf2)
    else TyFun (tf1, change2 t1 t2 tf2)
    | TyList typ -> TyList (change2 t1 t2 typ)
    | _ -> t

let rec change : typ -> typ -> subst -> subst -> subst
= fun t1 t2 s1 s2 ->
  match s1 with
    | [] -> s2
    | (a,t)::tl -> if occur t1 t then change t1 t2 tl (s2 @ [(a, change2 t1 t2 t)])
    else change t1 t2 tl (s2 @ [(a,t)])

let rec unify : typ -> typ -> subst -> subst
= fun t1 t2 s ->
  match t1, t2 with
    | TyUnit, TyUnit -> s
    | TyInt, TyInt -> s
    | TyBool, TyBool -> s
    | TyVar a, typ ->
      begin match typ with
        | TyVar b -> if a = b then s else extend_subst (a, TyVar b) (change t1 t2 s empty_subst)
        | t -> if occur (TyVar a) t then raise TypeError else extend_subst (a, t) (change t1 t2 s empty_subst)
      end
    | t, TyVar a -> unify (TyVar a) t s
    | TyFun (t1, t2), TyFun (tp1, tp2) ->
      let s1 = unify t1 tp1 s in
      let s2 = unify (substitution t2 s1) (substitution tp2 s1) s1 in s2
    | TyList t1, TyList t2 -> unify t1 t2 s
    | _, _ -> raise TypeError

let rec unifyall : tyeqn -> subst -> subst
= fun te s ->
  match te with
    | [] -> s
    | (t1,t2)::u -> let s1 = unify (substitution t1 s) (substitution t2 s) s in unifyall u s1

let solve : tyeqn -> subst
= fun u -> unifyall u empty_subst

let typeof : exp -> typ 
=fun exp ->
  let a = fresh_tyvar () in
  let s = solve (v empty_tyenv exp a) in
  substitution a s;;


(* Feedback *)


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

exception TypeError

type typ = 
    TyUnit 
  | TyInt 
  | TyBool 
  | TyFun of typ * typ 
  | TyList of typ
  | TyVar of tyvar
and tyvar = string


(* You can invoke "fresh_tyvar()" to generate a fresh type variable *)
let tyvar_num = ref 0
let fresh_tyvar () = (tyvar_num := !tyvar_num + 1; (TyVar ("t" ^ string_of_int !tyvar_num)))

let rec map : ('a -> 'b) -> 'a list -> 'b list
= fun f l ->
  match l with
  | [] -> []
  | hd::tl -> (f hd)::(map f tl)

let rec for_all : ('a -> bool) -> 'a list -> bool
= fun f l ->
  match l with
  | [] -> true
  | hd::tl -> if f hd then for_all f tl else false

let rec fold_left : ('b -> 'a -> 'b) -> 'b -> 'a list -> 'b
= fun f accu l ->
  match l with
  | [] -> accu
  | hd::tl -> fold_left f (f accu hd) tl

module TEnv = struct
  type t = var -> typ

  let empty : t
  = fun _ -> raise TypeError

  let find : t -> var -> typ
  = fun tenv x -> tenv x

  let extend : (var * typ) -> t -> t
  = fun (x, t) tenv -> fun y -> if x = y then t else (tenv y)
end

module Subst = struct 
  type t = (tyvar * typ) list

  let empty = []

  let rec find : t -> tyvar -> typ -> typ
  = fun subst x typ ->
    match subst with
    | [] -> typ
    | (y, ty)::tl -> if x = y then ty else find tl x typ

  let rec apply : typ -> t -> typ
  = fun typ subst ->
    match typ with
    | TyUnit
    | TyInt
    | TyBool -> typ
    | TyFun (t1, t2) -> TyFun (apply t1 subst, apply t2 subst)
    | TyList t -> TyList (apply t subst)
    | TyVar x -> find subst x typ

  let extend : (tyvar * typ) -> t -> t
  = fun (tv, ty) subst -> (tv, ty)::(map (fun (x, t) -> (x, apply t [(tv, ty)])) subst)
end

let eq_vars = ref []
let rec gen_equations : TEnv.t -> exp -> typ -> (typ * typ) list
= fun tenv e ty ->
  match e with
  | UNIT
  | PRINT _ -> [(ty, TyUnit)]
  | TRUE
  | FALSE -> [(ty, TyBool)]
  | CONST _ -> [(ty, TyInt)]
  | VAR x -> [(ty, TEnv.find tenv x)]
  | ADD (e1, e2)
  | SUB (e1, e2)
  | MUL (e1, e2)
  | DIV (e1, e2) -> (ty, TyInt) :: (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt)
  | EQUAL (e1, e2) ->
    let tyvar = fresh_tyvar () in
    eq_vars := tyvar::!eq_vars;
    (ty, TyBool) :: (gen_equations tenv e1 tyvar) @ (gen_equations tenv e2 tyvar)
  | LESS (e1, e2) -> (ty, TyBool) :: (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt)
  | NOT e -> (ty, TyBool) :: (gen_equations tenv e TyBool)
  | NIL -> let tyvar = fresh_tyvar () in [(ty, TyList tyvar)]
  | CONS (e1, e2) ->
    let tyvar = fresh_tyvar () in
    (ty, TyList tyvar) :: (gen_equations tenv e1 tyvar) @ (gen_equations tenv e2 (TyList tyvar))
  | APPEND (e1, e2) ->
    let tyvar = fresh_tyvar () in
    (ty, TyList tyvar) :: (gen_equations tenv e1 (TyList tyvar)) @ (gen_equations tenv e2 (TyList tyvar))
  | HEAD e ->
    let tyvar = fresh_tyvar () in
    (ty, tyvar) :: (gen_equations tenv e (TyList tyvar))
  | TAIL e ->
    let tyvar = fresh_tyvar () in
    (ty, TyList tyvar) :: (gen_equations tenv e (TyList tyvar))
  | ISNIL e ->
    let tyvar = fresh_tyvar () in
    (ty, TyBool) :: (gen_equations tenv e (TyList tyvar))
  | IF (e1, e2, e3) -> (gen_equations tenv e1 TyBool) @ (gen_equations tenv e2 ty) @ (gen_equations tenv e3 ty)
  | LET (x, e1, e2) ->
    let tyvar = fresh_tyvar () in
    (gen_equations tenv e1 tyvar) @ (gen_equations (TEnv.extend (x, tyvar) tenv) e2 ty)
  | LETREC (f, x, e1, e2) ->
    let arg_ty = fresh_tyvar () in
    let res_ty = fresh_tyvar () in
    let tenv = TEnv.extend (f, TyFun (arg_ty, res_ty)) (TEnv.extend (x, arg_ty) tenv) in
    (gen_equations tenv e1 res_ty) @ (gen_equations tenv e2 ty)
  | LETMREC ((f, x, fbody), (g, y, gbody), e) ->
    let f_arg_ty = fresh_tyvar () in
    let f_res_ty = fresh_tyvar () in
    let g_arg_ty = fresh_tyvar () in
    let g_res_ty = fresh_tyvar () in
    let tenv = TEnv.extend (f, TyFun (f_arg_ty, f_res_ty)) (TEnv.extend (x, f_arg_ty) tenv) in
    let tenv = TEnv.extend (g, TyFun (g_arg_ty, g_res_ty)) (TEnv.extend (y, g_arg_ty) tenv) in
    (gen_equations tenv fbody f_res_ty) @ (gen_equations tenv gbody g_res_ty) @ (gen_equations tenv e ty)
  | PROC (x, e) ->
    let arg_ty = fresh_tyvar () in
    let res_ty = fresh_tyvar () in
    (ty, TyFun (arg_ty, res_ty)) :: (gen_equations (TEnv.extend (x, arg_ty) tenv) e res_ty)
  | CALL (e1, e2) ->
    let arg_ty = fresh_tyvar () in
    (gen_equations tenv e1 (TyFun (arg_ty, ty))) @ (gen_equations tenv e2 arg_ty)
  | SEQ (e1, e2) -> let tyvar = fresh_tyvar () in (gen_equations tenv e1 tyvar) @ (gen_equations tenv e2 ty)

let rec occurrence_check : tyvar -> typ -> bool
= fun x ty ->
  match ty with
  | TyUnit
  | TyInt
  | TyBool -> false
  | TyFun (ty1, ty2) -> occurrence_check x ty1 || occurrence_check x ty2
  | TyList ty -> occurrence_check x ty
  | TyVar y -> x = y

let rec unify : typ -> typ -> Subst.t -> Subst.t
= fun ty1 ty2 subst ->
  match ty1, ty2 with
  | TyVar x, TyVar y -> if x = y then subst else Subst.extend (x, ty2) subst
  | _, TyVar _ -> unify ty2 ty1 subst
  | TyVar x, _ ->
    if occurrence_check x ty2 then
      raise TypeError
    else
      Subst.extend (x, ty2) subst
  | TyInt, TyInt
  | TyBool, TyBool
  | TyUnit, TyUnit -> subst
  | TyList ty1, TyList ty2 -> unify ty1 ty2 subst
  | TyFun (f_arg_ty, f_res_ty), TyFun (g_arg_ty, g_res_ty) ->
    let subst = unify f_arg_ty g_arg_ty subst in
    let f_res_ty = Subst.apply f_res_ty subst in
    let g_res_ty = Subst.apply g_res_ty subst in
    unify f_res_ty g_res_ty subst
  | _ -> raise TypeError
  
let rec unify_all : (typ * typ) list -> Subst.t -> Subst.t
= fun eqns subst ->
  match eqns with
  | [] -> subst
  | (ty1, ty2)::tl ->
    let ty1 = Subst.apply ty1 subst in
    let ty2 = Subst.apply ty2 subst in
    let subst = unify ty1 ty2 subst in
    unify_all tl subst

let solve : (typ * typ) list -> Subst.t
= fun eqns ->
  let subst = unify_all eqns Subst.empty in
  fold_left (fun subst ty ->
    let ty = Subst.apply ty subst in
    match ty with
    | TyInt
    | TyBool -> subst
    | TyVar _ -> unify ty TyInt subst
    | _ -> raise TypeError
  ) subst !eq_vars

let typeof : exp -> typ
= fun e ->
  let ty = fresh_tyvar () in
  let _ = eq_vars := [] in
  let eqns = gen_equations TEnv.empty e ty in
  let subst = solve eqns in
  Subst.apply ty subst
