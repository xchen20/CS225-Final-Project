(* Name: <your name> *)
(* Course: UVM CS 225 Spring 2018 - Darais *)
(* HW: HW4 *)

open Util
open StringSetMap

(* The Assignment:
 *
 * Fill in the `raise TODO` parts of the code:
 * - 30 cases in the `step` function
 * - 5 cases in the `infer` function
 *
 * See the writeup for the specification for `step` and `infer` functions that
 * you must implement.
 *
 * Passing all of the tests does not guarantee 100%. You may want to write some
 * tests of your own.
 *)

exception NOT_FOUND

(* ℓ ∈ loc ≈ ℕ
 *)
type var = string
[@@deriving show {with_path = false}]

(* Expressions.
 *
 * e ∈ exp ⩴ true | false | if(e){e}{e}
 *         | ⟨e,e⟩ | projl(e) | projr(e)
 *         | ref(e) | !e | e ≔ e | e ; e
 *         | loc(ℓ) | Error | Try t with t
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


let subst (x : string) (t : ty) (e2 : exp) (e1 : exp) : exp =
  match unique_vars (App(Lam(x,t,e1),e2)) with
  | App(Lam(x',_,e1'),e2') -> subst_r x' e2' e1'
  | _ -> raise IMPOSSIBLE


(* Values.
 * v ∈ value ⩴ true | false
 *           | ⟨v,v⟩
 *           | loc(ℓ)
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

let rec step (e0 : exp): result = match e0 with
  | True -> Val(VTrue)
  | False -> Val(VFalse)
  | Var(_) -> Stuck
  | Lam(var,e0) -> Val(VLam(var,e0))
  | App(e1,e2) -> begin match step e1 with
    | Val(v1) -> begin match step e2 with
      | Val(v2) -> begin match v1 with
        (* —————————————————————(β)
         * (λx:τ.e)v —→ [x ↦ v]e
         *)
        | VLam(x,t,e) -> Step(subst x t (exp_of_value v2) e)
        | _ -> Stuck
        end
      (*   e₂ —→ e₂′
       * —————————————
       * v₁ e₂ —→ v₁ e₂′
       *)
      | Step(e2') -> Step(App(e1,e2'))
      | Stuck -> Stuck
      end
    (*    e₁ —→ e₁′
     * ———————————————
     * e₁ e₂ —→ e₁′ e₂
     *)
    | Step(e1') -> Step(App(e1',e2))
    | Stuck -> Stuck
    | Step(App(Error,e)) -> Step(Error)
    | Step(App(v,Error)) -> Step(Error)
    | Step(Error) -> Stuck
    end
  | TryWith(v1,e2) -> begin match step v1 with
    | Step(v) -> Step(Val())
    | Step() -> Step()
    | Step(e1') -> Step(TryWith(e1',e2))
    | Stuck -> Stuck
    end

(* The reflexive transitive closure of the small-step semantics relation *)
let rec step_star (e : exp) (s : store) : exp * store = match step e s with
  | Val(v) -> (exp_of_val v,s)
  | Step(e',s') -> step_star e' s'
  | Stuck -> (e,s)

(* Types.
 *
 * τ ∈ ty ⩴ bool
 *        | τ × τ
 *        | ref(τ)
 *)
type ty =
  | Bool
  | Error
[@@deriving show {with_path = false}]


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
    | Terror(x) -> t
    | Ttry(e1,e2) ->
        let t1 = infer e1 in
        let t2 = infer e2 in
        if (t1 = t2) then t else Error



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

(* Name: <your name> *)
