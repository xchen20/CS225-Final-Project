(* Name: Xiaosong Chen & Wyatt Wu *)
(* Course: UVM CS 225 Spring 2018 - Darais *)
(* HW: checkpoint*)

open Util
open StringSetMap


exception NOT_FOUND

type var = string
[@@deriving show {with_path = false}]

(* Types.
 *
 * τ ∈ ty ⩴ bool
 *        | Error
 *)
type ty =
  | Bool
  | Unknown
[@@deriving show {with_path = false}]

(* Expressions.
 *
 * e ∈ exp ⩴ true | false | Error | Try t with t
 *)
type exp =
  | True
  | False
  | Error of ty
  | If of exp * exp * exp
  | TryWith of exp * exp
  | Var of var
  | Lam of var * ty * exp
  | App of exp * exp
[@@deriving show {with_path = false}]

let rec free_vars (e0 : exp) : string_set = match e0 with
  | True -> StringSet.empty
  | False -> StringSet.empty
  | If(e1,e2,e3) ->
      StringSet.union (StringSet.union (free_vars e1) (free_vars e2))
       (free_vars e3)
   | Var(x) -> StringSet.of_list [x]
   | Lam(x,t,e) -> StringSet.remove x (free_vars e)
   | App(e1,e2) -> StringSet.union (free_vars e1) (free_vars e2)

(* Helper function for
*  beta rule in lambda calculus
*  Not finish yet, will still working on that.
*  Enforces global uniqueness of variables.
*)
let unique_vars (e : exp) : exp =
  let new_var (iO : int option) (x : string) : string = match iO with
      | None -> x
      | Some(i) -> x ^ string_of_int i
  in
  let next_var (iO : int option) : int option = match iO with
      | None -> Some(1)
      | Some(i) -> Some(i+1)
  in
  let rec rename_var_r
    (iO : int option)
    (x : string)
    (g : string_set)
    : string * string_set =
      let x' = new_var iO x in
      if StringSet.mem x' g
      then rename_var_r (next_var iO) x g
      else (x',StringSet.add x' g)
  in
  let rename_var = rename_var_r None in
  let rec unique_vars_r
    (e0 : exp)
    (env : string string_map)
    (g : string_set)
    : exp * string_set =
      match e0 with
      | True -> (True,g)
      | False -> (False,g)
      | If(e1,e2,e3) ->
          let (e1',g'1) = unique_vars_r e1 env g in
          let (e2',g'2) = unique_vars_r e2 env g'1 in
          let (e3',g'3) = unique_vars_r e3 env g'2 in
          (If(e1',e2',e3'),g'3)
      | Var(x) -> (Var(StringMap.find x env),g)
      | Lam(x,t,e) ->
          let (x',g') = rename_var x g in
          let (e',g'') = unique_vars_r e (StringMap.add x x' env) g' in
          (Lam(x',t,e'),g'')
      | App(e1,e2) ->
          let (e1',g') = unique_vars_r e1 env g in
          let (e2',g'') = unique_vars_r e2 env g' in
          (App(e1',e2'),g'')
  in
  let initial_env (ss : string_set) =
    List.fold_right (fun x -> StringMap.add x x) (StringSet.elements ss) StringMap.empty
  in
  let fvs : string_set = free_vars e in
  let (e',_) = unique_vars_r e (initial_env fvs) fvs in
  e'

(* Values.
 * v ∈ value ⩴ true | false
 *           | Lam
 *)
type value =
  | VTrue
  | VFalse
  | VError of ty
  | VLam of var * ty * exp
[@@deriving show {with_path = false}]
 exception TYPE_ERROR
(* Typing relation encoded as an inference metafunction. *)
let rec infer (e : exp) : ty = match e with
    | True -> Bool
    | False -> Bool
    | If(e1,e2,e3) ->
        let t1 = infer e1 in
        let t2 = infer e2 in
        let t3 = infer e3 in
        if not (t1 = Bool) then raise TYPE_ERROR else
        if not (t2 = t3) then raise TYPE_ERROR else
        t2
    (*
     *  Γ ⊢error:T   (T-Error)
     *)
    | Error(t) -> t
    (*
    *  Γ ⊢t1 :T  Γ ⊢t2 :T
    *    —————————————       (T-Try)
    *  Γ ⊢tryt1 witht2 :T
    *)
    | TryWith(e1,e2) ->
        let t1 = infer e1 in
        let t2 = infer e2 in
        if not (t1 = t2) then raise TYPE_ERROR else t2

let rec exp_of_val (v : value) : exp = match v with
  | VTrue -> True
  | VFalse -> False
  | VError(t) -> Error(t)
  | VLam(x,t,e) -> Lam(x,t,e)

(* r ∈ result ⩴ v | ⟨e,s⟩ | stuck
 *)
type result =
  | Val of value
  | Step of exp
  | Stuck
[@@deriving show {with_path = false}]
 let rec subst_r (x : string) (e2 : exp) (e10 : exp) : exp = match e10 with
   | True -> True
   | False -> False
   | If(e11,e12,e13) -> If(subst_r x e2 e11,subst_r x e2 e12,subst_r x e2 e13)
   | Var(y) -> if x = y then e2 else Var(y)
   | Lam(y,t,e1) -> Lam(y,t,subst_r x e2 e1)
   | App(t11,t12) -> App(subst_r x e2 t11,subst_r x e2 t12)
   (* New cases *)
 
 let subst (x : string) (t : ty) (e2 : exp) (e1 : exp) : exp =
   match unique_vars (App(Lam(x,t,e1),e2)) with
   | App(Lam(x',_,e1'),e2') -> subst_r x' e2' e1'
   | _ -> raise IMPOSSIBLE
(* The small-step relation e —→ e
 *
 * Assumption: e is closed.
 *
 * If step(e) = v, then e is a value (and does not take a step).
 * (i.e., e ∈ val)
 *
 * If step(e) = e′, then e steps to e′.
 * (i.e., e —→ e′)
 *
 * If step(e) = stuck, then e is stuck, that is e is not a value and does not
 * take a step.
 * (i.e., e ∉ val and e —↛)
 *)
let rec step (e0 : exp): result = match e0 with
  | True -> Val(VTrue)
  | False -> Val(VFalse)
  | Error(t) -> Val(VError(t))
  | Var(_) -> Stuck
  | Lam(var,t,e0) -> Val(VLam(var,t,e0))
  | App(e1,e2) -> begin match step e1 with
    | Val(VError(t)) -> Step(Error(Unknown))
    | Val(v1) -> begin match step e2 with
      | Val(VError(t)) -> Step(Error(Unknown))
      | Val(v2) -> begin match v1 with
        (* —————————————————————(β)
         * (λx:τ.t)v —→ [x ↦ v]t
         *)
        | VLam(x,t,e) -> Step(subst x t (exp_of_val v2) e)
        | _ -> Stuck
        end
      (*   t₂ —→ t₂′
       * —————————————
       * v₁ e₂ —→ v₁ e₂′
       *)
      | Step(e2') -> Step(App(e1,e2'))
      | Stuck -> Stuck
      end
    (*    t₁ —→ t₁′
     * ———————————————
     * t₁ t₂ —→ t₁′ t₂
     *)
    | Step(e1') -> Step(App(e1',e2))
    | Stuck -> Stuck
(*
    (*  error t2 → error
     *)
    | Step(App(Error,e)) -> Step(Error)

    (*  v1 error → error
     *)
    | Step(App(v,Error)) -> Step(Error)
    | Step(Error) -> Stuck
  *)
    end
  | TryWith(e1,e2) -> begin match step e1 with
    (* try error with t2 → t2
     *)
    | Val(VError(t)) -> Step(e2)
    (*  try v1 with t2 → v1
     *)
    | Val(v1) -> Step(exp_of_val v1)
    (*     t1 →t′1
     *  —————————————  → try t′1 with t2
        try t1 with t2
     *)
    | Step(e1') -> Step(TryWith(e1',e2))
    | Stuck -> Stuck
    end

(* The reflexive transitive closure of the small-step semantics relation *)
let rec step_star (e : exp) : exp = match step e with
  | Val(v) -> (exp_of_val v)
  | Step(e') -> step_star e'
  | Stuck -> (e)

(*
* Test Caes: not done yet, we have to spend more time on testing make sure they are passed
*)
let step_tests : test_block =
  TestBlock
  ( "STEP"
  , [ True,                                          Val(VTrue)
    ; False,                                         Val(VFalse)
    ; Error(Bool),                                   Val(VError(Bool))
    ; Var("x"),                                      Stuck
    ; App(Lam("x",Bool,Var("x")),True),              Step(True)
    ; App(Error(Bool),True),                         Step(Error(Unknown))
    ; App(True,Error(Bool)),                         Step(Error(Unknown))
    ; TryWith(Error(Bool),True),                     Step(True)
    ; TryWith(True,False),                           Step(True)
    ]
  , (fun (e) -> step e )
  , [%show : exp]
  , [%show : result]
  )

let infer_tests =
  TestBlock
  ( "INFER"
  , [ True,                                          Bool
    ; False,                                         Bool
    ; Error(Bool),                                   Bool
    ; If(True,False,True),                           Bool
    ; If(Error(Bool),Error(Unknown),Error(Unknown)), Unknown
    ; TryWith(Error(Bool),True),                     Bool
    ; TryWith(True, Error(Bool)),                    Bool
    ]
  , (fun e -> infer e )
  , (fun e -> [%show : exp] (e))
  , [%show : ty]
  )

let _ =
  _SHOW_PASSED_TESTS := false ;
  run_tests [step_tests;infer_tests]

(* Name: Xiaosong Chen & Wyatt Wu *)
