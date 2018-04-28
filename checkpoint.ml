(* Name: Xiaosong Chen & Wyatt Wu *)
(* Course: UVM CS 225 Spring 2018 - Darais *)
(* HW: checkpoint*)

open Util
open StringSetMap


exception NOT_FOUND

type var = string
[@@deriving show {with_path = false}]

(* Expressions.
 *
 * e ∈ exp ⩴ true | false | Error | Try t with t
 *)
type exp =
  | True
  | False
  | Error
  | If of exp * exp * exp
  | TryWith of exp * exp
  | Var of var
  | Lam of var * exp
  | App of exp * exp
[@@deriving show {with_path = false}]


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
  | VLam of var * exp
[@@deriving show {with_path = false}]

let rec exp_of_val (v : value) : exp = match v with
  | VTrue -> True
  | VFalse -> False
  | VLam(x,e) -> Lam(x,e)

(* r ∈ result ⩴ v | ⟨e,s⟩ | stuck
 *)
type result =
  | Val of value
  | Step of exp
  | Stuck
[@@deriving show {with_path = false}]

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
  | Var(_) -> Stuck
  | Lam(var,e0) -> Val(VLam(var,e0))
  | App(e1,e2) -> begin match step e1 with
    | Val(v1) -> begin match step e2 with
      | Val(v2) -> begin match v1 with
        (* —————————————————————(β)
         * (λx:τ.t)v —→ [x ↦ v]t
         *)
        | VLam(x,t,e) -> Step(subst x t (exp_of_value v2) e)
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

    (*  error t2 → error
     *)
    | Step(App(Error,e)) -> Step(Error)

    (*  v1 error → error
     *)
    | Step(App(v,Error)) -> Step(Error)
    | Step(Error) -> Stuck
    end
  | TryWith(v1,e2) -> begin match step v1 with
    (*  try v1 with t2 → v1
     *)
    | Val(v1) -> Step(exp_of_val v1)
    (* try error with t2 → t2
     *)
    | Val(Error) -> Step(exp_of_val e2)
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

(* Types.
 *
 * τ ∈ ty ⩴ bool
 *        | Error
 *)
type ty =
  | Bool
  | Error
[@@deriving show {with_path = false}]


(* Typing relation encoded as an inference metafunction. *)
let rec infer (e : exp) : ty = match e with
    | True -> Bool
    | False -> Bool
    | If(e1,e2,e3) ->
        let t1 = infer e1 in
        let t2 = infer e2 in
        let t3 = infer e3 in
        if not (t1 = Bool) then Error else
        if not (t2 = t3) then Error else
        t2
    (*
     *  Γ ⊢error:T   (T-Error)
     *)
    | Terror(x) -> t
    (*
    *  Γ ⊢t1 :T  Γ ⊢t2 :T
    *    —————————————       (T-Try)
    *  Γ ⊢tryt1 witht2 :T
    *)
    | Ttry(e1,e2) ->
        let t1 = infer e1 in
        let t2 = infer e2 in
        if (t1 = t2) then t else Error


(*
* Test Caes: not done yet, we have to spend more time on testing make sure they are passed
*)
let step_tests : test_block =
  let s1 : store = [(1,VTrue);(2,VFalse)] in
  let s2 : store = [(1,VTrue);(2,VTrue)] in
  TestBlock
  ( "STEP"
  , [ (True,s1)                                              , Val(VTrue)
    ; (False,s1)                                             , Val(VFalse)
    ; (If(True,False,True),s1)                               , Step(False,s1)
    ; (If(False,False,True),s1)                              , Step(True,s1)
    ; (If(Pair(True,False),True,False),s1)                   , Stuck
    ; (If(Assign(Loc(2),True),False,True),s1)                , Step(If(True,False,True),s2)
    ; (If(Deref(True),True,False),s1)                        , Stuck
    ; (Pair(True,False),s1)                                  , Val(VPair(VTrue,VFalse))
    ; (Pair(Assign(Loc(2),True),True),s1)                    , Step(Pair(True,True),s2)
    ; (Pair(True,Assign(Loc(2),True)),s1)                    , Step(Pair(True,True),s2)
    ; (Pair(Deref(True),True),s1)                            , Stuck
    ; (Pair(True,Deref(True)),s1)                            , Stuck
    ; (Projl(Pair(True,False)),s1)                           , Step(True,s1)
    ; (Projl(True),s1)                                       , Stuck
    ; (Projl(If(True,Pair(True,False),Pair(False,True))),s1) , Step(Projl(Pair(True,False)),s1)
    ; (Projl(Deref(True)),s1)                                , Stuck
    ; (Projr(Pair(True,False)),s1)                           , Step(False,s1)
    ; (Projr(True),s1)                                       , Stuck
    ; (Projr(If(True,Pair(True,False),Pair(False,True))),s1) , Step(Projr(Pair(True,False)),s1)
    ; (Projr(Deref(True)),s1)                                , Stuck
    ; (Ref(True),s1)                                         , Step(Loc(3),s1 @ [(3,VTrue)])
    ; (Ref(Assign(Loc(2),True)),s1)                          , Step(Ref(True),s2)
    ; (Ref(Deref(True)),s1)                                  , Stuck
    ; (Deref(Loc(2)),s1)                                     , Step(False,s1)
    ; (Deref(True),s1)                                       , Stuck
    ; (Deref(If(True,Loc(1),Loc(2))),s1)                     , Step(Deref(Loc(1)),s1)
    ; (Deref(Deref(True)),s1)                                , Stuck
    ; (Assign(Loc(2),True),s1)                               , Step(True,s2)
    ; (Assign(True,False),s1)                                , Stuck
    ; (Assign(If(False,Loc(1),Loc(2)),True),s1)              , Step(Assign(Loc(2),True),s1)
    ; (Assign(Loc(1),Assign(Loc(2),True)),s1)                , Step(Assign(Loc(1),True),s2)
    ; (Assign(Deref(False),True),s1)                         , Stuck
    ; (Assign(Loc(1),Deref(False)),s1)                       , Stuck
    ; (Sequence(True,False),s1)                              , Step(False,s1)
    ; (Sequence(Assign(Loc(2),True),Deref(Loc(2))),s1)       , Step(Sequence(True,Deref(Loc(2))),s2)
    ; (Sequence(Deref(True),False),s1)                       , Stuck
    ]
  , (fun (e,s) -> step e s)
  , [%show : exp * store]
  , [%show : result]
  )

let infer_tests =
  let st : store_ty = [(1,Bool);(2,Prod(Bool,Bool));(3,Ref(Bool))] in
  TestBlock
  ( "INFER"
  , [ True                                                 , Bool
    ; False                                                , Bool
    ; If(True,False,True)                                  , Bool
    ; If(True,Pair(True,Ref(False)),Pair(False,Ref(True))) , Prod(Bool,Ref(Bool))
    ; Projl(Pair(True,Ref(False)))                         , Bool
    ; Projr(Pair(True,Ref(False)))                         , Ref(Bool)
    ; Ref(True)                                            , Ref(Bool)
    ; Ref(Loc(1))                                          , Ref(Ref(Bool))
    ; Deref(Loc(1))                                        , Bool
    ; Deref(Loc(2))                                        , Prod(Bool,Bool)
    ; Deref(Deref(Loc(3)))                                 , Bool
    ; Assign(Loc(1),False)                                 , Bool
    ; Assign(Loc(2),Pair(True,False))                      , Bool
    ; Sequence(Assign(Loc(1),False),Ref(True))             , Ref(Bool)
    ]
  , (fun e -> infer e st)
  , (fun e -> [%show : exp * store_ty] (e,st))
  , [%show : ty]
  )

let _ =
  _SHOW_PASSED_TESTS := false ;
  run_tests [step_tests;infer_tests]

(* Name: Xiaosong Chen & Wyatt Wu *)
