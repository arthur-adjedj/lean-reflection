import Reflection.Vec
import Reflection.UnifyCmd
import Reflection.DelabStructs
import Reflection.Simple.Constructors
import Reflection.Simple.RecursorScaffolding

set_option pp.proofs true

inductive IotaCasesScaffolding2 {motive : T -> Prop} (o_ctors : Vec (SCtor T) K)
  : (i : Nat /- actually `Fin k` -/) -> (ctors : Vec (SCtor T) i) -> (base : RecCases motive ctors) -> Type 2
| ground
  (base : RecCases motive ⟦⟧)
  : IotaCasesScaffolding2 o_ctors 0 ⟦⟧ base
| after
  (ctor : SCtor T)
  {ctors' : Vec (SCtor T) i'}
  (base : RecCases motive (ctor ::: ctors'))
  :
  (sub : (case : RecCase motive ctor ctor id (RecCaseScaffold ctor))
    -> IotaCasesScaffolding2 o_ctors i' ctors' (base case)
  )
    -> IotaCasesScaffolding2 o_ctors (.succ i') (ctor ::: ctors') (base)

def IotaCasesScaffold2 {motive : T -> Prop} (o_ctors : Vec (SCtor T) K) 
  : (i : Nat) -> (ctors : Vec (SCtor T) i) -> (base : RecCases motive ctors) -> IotaCasesScaffolding2 (motive := motive) o_ctors i ctors base
| .zero   ,              ⟦⟧, base => .ground base
| .succ i', ctor ::: ctors', base => .after ctor base (fun case => IotaCasesScaffold2 o_ctors i' ctors' (base case))

/-- The cases after caseₖ -/
def IotaCases2
  (o_ctors : Vec (SCtor T) K)
  (recursor : Rec o_ctors)
  (motive : T -> Prop)
  (body : (base : RecCases motive ⟦⟧) -> Prop)
  :
  (ctors : Vec (SCtor T) i) ->
  {base : RecCases motive ctors} ->
  IotaCasesScaffolding2 (motive := motive) o_ctors i ctors base -> Prop
| ⟦⟧,           _, .ground base         => body base
| _ ::: ctors', _, .after ctor base sub =>
  (case : RecCase motive ctor ctor id (RecCaseScaffold ctor)) ->
    @IotaCases2 _ _ _ o_ctors recursor motive body ctors' (base case) (sub case)

#reduce IotaCases2
#reduce IotaCases2 ⟦⟧ sorry (fun t => t = t) (fun base => sorry)
#reduce IotaCases2 ⟦⟧ sorry (fun t => t = t) (fun base => base = base) ⟦⟧

/-- Doesn't do much, just skips some ctors before thiscase. -/
inductive IotaCasesScaffolding1 {motive : T -> Prop} (o_ctors : Vec (SCtor T) K) (k : Fin K)
  : (i : Nat) -> (ctors : Vec (SCtor T) i) -> Type 2
| thiscase (ctors : Vec (SCtor T) (.succ k)) : IotaCasesScaffolding1 o_ctors k (.succ k) ctors
| before
  (ctor : SCtor T)
  (ctors' : Vec (SCtor T) i')
  :
  (sub : (case : RecCase motive ctor ctor id (RecCaseScaffold ctor))
          -> IotaCasesScaffolding1 o_ctors k i' ctors')
    -> IotaCasesScaffolding1 o_ctors k (.succ i') (ctor ::: ctors')

theorem aux_indices : i + 1 > k -> ¬(i = k) -> i > k
| h₁, h₂ => by
  simp_all [GT.gt]
  cases h₁ with
  | refl => simp_all [Nat.add]
  | step o => simp_all [Nat.add]; exact o

/-- Build the scaffolding from K to k. -/
def IotaCasesScaffold1 {motive : T -> Prop} (o_ctors : Vec (SCtor T) K) (k : Fin K)
  : IotaCasesScaffolding1 (motive := motive) o_ctors k K o_ctors
  := go ⟨K, by simp [k.isLt]⟩ o_ctors -- start with all ctors and go until ctorₖ.
where
  go {motive : T -> Prop} {o_ctors : Vec (SCtor T) K} {k : Fin K}
  : (i : {i : Nat // i > k}) -> (ctors : Vec (SCtor T) i) -> IotaCasesScaffolding1 (motive := motive) o_ctors k i ctors
  | ⟨.succ i', hi'⟩, ctor ::: (ctors' : Vec (SCtor T) i') =>
    if h : i' = k.val then by
      subst h
      exact .thiscase (motive := motive) (o_ctors := o_ctors) (ctor ::: ctors')
    else
      let xxx : IotaCasesScaffolding1 o_ctors k i' ctors'
        := go (motive := motive) (o_ctors := o_ctors) (k := k) ⟨i', aux_indices hi' h⟩ ctors'
      .before ctor ctors' (fun _ => xxx)

/-- Introduces binders for each case.
  Uppercase `K` is the amount of constructors.
  Lowercase `k` is the constructor for which we want to compute the iota rule type.
  ```lean
  (c₀ : RecCase ...) ->
  (c₁ : RecCase ...) ->
  ...
  (c_{K-1} : RecCase ...) ->
    body (recursor motive c₀ c₁ ... c_{K-1}) cₖ
  ```
 -/
def IotaCases1
  (o_ctors : Vec (SCtor T) K)
  (recursor : Rec o_ctors)
  (motive : T -> Prop)
  (k : Fin K)
  {ctors : Vec (SCtor T) i}
  (base : RecCases motive ctors) -- we give it `recursor motive` as start!
  : IotaCasesScaffolding1 (motive := motive) o_ctors k i ctors ->
    (body :
      (ctorₖ : SCtor T) ->
      RecCase motive ctorₖ ctorₖ id (RecCaseScaffold ctorₖ) ->
      RecCases motive ⟦⟧ ->
      Prop
    ) ->
    Prop
| .thiscase ctors, body =>
  let (ctorₖ ::: ctors') := ctors
  (caseₖ : RecCase motive ctorₖ ctorₖ id (RecCaseScaffold ctorₖ)) ->
    IotaCases2 o_ctors recursor motive (body ctorₖ caseₖ) ctors' (IotaCasesScaffold2 o_ctors k ctors' (base caseₖ))
| .before (i' := i') ctor ctors' sub, body =>
  (case : RecCase motive ctor ctor id (RecCaseScaffold ctor)) ->
    IotaCases1 (ctors := ctors') o_ctors recursor motive k (base case) (sub case) body

-- TODO: dumb idea, but you could take a `RecCaseScaffold _` as parameter to IotaArgs, and then pass it to `caseₖ`, **and also pattern match on it**, thus obtaining the constraints you need!
-- But it^ maybe shouldn't be necessary. Below `c x` should work at least for the nonrecursive case...
def IotaArgs {motive : T -> Prop} (o_ctor : SCtor T) (base : RecCases motive ⟦⟧)
  :
  -- (ctorₖ : SCtor T) ->
  (spec : SCtorSpec) ->
  (ctor : SCtorType T spec) ->
  (args : SCtorArgs T spec ctor) ->
  (mots : Prop -> Prop) ->
  (scaffolding : @RecCaseScaffolding T motive o_ctor spec ctor args mots) ->
  (caseₖ : RecCase motive o_ctor ⟨spec, ctor, args⟩ mots scaffolding) ->
  (demotivate : {P : Prop} -> mots P -> P) ->
  (body : (t : T) -> (rhs : motive t) -> Prop) ->
  Prop
  | .nil          , t   , .head _           , _   , .ground       _ _  , caseₖ, demotivate, body =>
    let rhs : motive t := demotivate caseₖ
    body t rhs
    -- We need the rhs to become something like `caseₖ a₁ a₂ ... (base ar₁) (base ar₂) ...`
    -- The type of just `caseₖ a₁ a₂ ...` is `RecCase o_ctor [] mots`

  | .other U spec', ctor, .nonrecursive args, mots, .nonrecursive _ sub, caseₖ, demotivate, body =>
    (a : U) ->
      -- I don't know why lean isn't able to typecheck through definitions in this specific case?
      have : RecCase motive o_ctor ⟨.other U spec', ctor, .nonrecursive args⟩ mots (.nonrecursive mots sub)
        = ((a : U) -> RecCase motive o_ctor ⟨spec', ctor a, args a⟩ mots (sub a))
        := by simp [RecCase, RecCase.go]
      have xxx : RecCase motive o_ctor ⟨spec', ctor a, args a⟩ mots (sub a) := (this ▸ caseₖ) a
      IotaArgs o_ctor base spec' (ctor a) (args a) mots (sub a) xxx demotivate body

  | .self    spec', ctor, .recursive args   , mots, .recursive    _ sub, caseₖ, demotivate, body =>
    (a : T) ->
      have : RecCase motive o_ctor ⟨.self spec', ctor, .recursive args⟩ mots (.recursive mots sub)
        = ((a : T) -> RecCase motive o_ctor ⟨spec', ctor a, args a⟩ _ (sub a))
        := by simp [RecCase, RecCase.go]
      let caseₖ' : RecCase motive o_ctor ⟨spec', ctor a, args a⟩ (fun P => mots (motive a → P)) (sub a)
        := (this ▸ caseₖ) a
      let demotivate' : (P : Prop) -> (mots (motive a → P)) → P
        := fun P p => demotivate p (base a)
      IotaArgs o_ctor base spec' (ctor a) (args a) (fun P => mots (motive a → P)) (sub a)
        caseₖ'
        @demotivate'
        body

def Iota (ctors : Vec (SCtor T) K) (recursor : Rec ctors) (k : Fin K) : Prop :=
  (motive : T -> Prop) ->
    IotaCases1 ctors recursor motive k (recursor motive) (IotaCasesScaffold1 ctors k) fun ctorₖ caseₖ base =>
      IotaArgs ctorₖ base ctorₖ.spec ctorₖ.ctor ctorₖ.args id (RecCaseScaffold ctorₖ) caseₖ id fun t rhs =>
        -- ListN.rec case_nil case_cons (ListN.cons x xs) = case_cons x xs (ListN.rec case_nil case_cons xs)
        -- ^^^^^^^^^^^ base ^^^^^^^^^^^                                     ^^^^^^^^^^^ base ^^^^^^^^^^^
        --                              ^^^^^^^ t ^^^^^^^
        base t = rhs

namespace Test
  class _SimpleInductiveType (T : Type) where
    K : Nat -- the amount of constructors
    ctors : Vec (SCtor T) K
    recursor : Rec ctors
    iotas : (k : Fin K) -> Iota ctors recursor k

  instance listNinst : _SimpleInductiveType ListN := {
    ctors :=
      ⟨.nil                   , ListN.nil,  cNil⟩ :::
      ⟨.other Nat (.self .nil), ListN.cons, cCons⟩ ::: ⟦⟧
    recursor := @ListN.rec
    iotas := fun
    | 0 => ListN.iota_cons
    | 1 => ListN.iota_nil
  }

  #unify Iota listNinst.ctors @ListN.rec 0 =?=
    (motive : ListN -> Prop) ->
    (case_nil : motive ListN.nil) ->
    (case_cons : (head : Nat) → (tail : ListN) → motive tail → motive (ListN.cons head tail)) ->
    (head : Nat) ->
    (tail : ListN) ->
    @ListN.rec motive case_nil case_cons (ListN.cons head tail)
        = case_cons head tail (@ListN.rec motive case_nil case_cons tail)

end Test

