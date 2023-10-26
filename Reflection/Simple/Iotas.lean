import Reflection.Vec
import Reflection.Simple.Constructors
import Reflection.Simple.RecursorScaffolding

-- Maybe move this after IotaCasesScaffolding1, since we might need the constraints from 1 for ctork?
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
  (sub : (case : @RecCase T ctor ctor.spec ctor.ctor ctor.args id motive (RecCaseScaffold ctor))
    -> IotaCasesScaffolding2 o_ctors i' ctors' (base case)
  )
    -> IotaCasesScaffolding2 o_ctors (.succ i') (ctor ::: ctors') (base)

def IotaCasesScaffold2 {motive : T -> Prop} (o_ctors : Vec (SCtor T) K) (k : Fin K) {ctors : Vec (SCtor T) k} (base : RecCases motive ctors)
  : IotaCasesScaffolding2 (motive := motive) o_ctors k ctors base
  := sorry

/-- The cases after caseₖ -/
def IotaCases2
  (o_ctors : Vec (SCtor T) K)
  (recursor : Rec o_ctors)
  (motive : T -> Prop)
  (body : (base : RecCases motive ⟦⟧) -> Prop)
  :
  (ctors : Vec (SCtor T) i) ->
  {base : RecCases motive ctors} ->
  IotaCasesScaffolding2 o_ctors i ctors base -> Prop
| ⟦⟧,           _, .ground base         => body base
| _ ::: ctors', _, .after ctor base sub =>
  (case : @RecCase T ctor ctor.spec ctor.ctor ctor.args id motive (RecCaseScaffold ctor)) ->
    @IotaCases2 _ _ _ o_ctors recursor motive body ctors' (base case) (sub case)

/-- Doesn't do much, just skips some ctors before thiscase. -/
inductive IotaCasesScaffolding1 {motive : T -> Prop} (o_ctors : Vec (SCtor T) K) (k : Fin K)
  : (i : Nat) -> (ctors : Vec (SCtor T) i) -> (base : RecCases motive ctors) -> Type 2
| thiscase
  (ctors : Vec (SCtor T) _)
  (base : RecCases motive ctors)
  -- For example when k=0, running ctors need to have a length of `(.succ k)`, so it checks out.
  : IotaCasesScaffolding1 o_ctors k (.succ k) ctors base
| before
  (ctor : SCtor T)
  {ctors' : Vec (SCtor T) i'}
  (base : RecCases motive (ctor ::: ctors'))
  :
  (sub : (case : @RecCase T ctor ctor.spec ctor.ctor ctor.args id motive (RecCaseScaffold ctor))
          -> IotaCasesScaffolding1 o_ctors k i' ctors' (base case))
    -> IotaCasesScaffolding1 o_ctors k (.succ i') (ctor ::: ctors') (base)

/-- Build the scaffolding from K to k. -/
def IotaCasesScaffold1 {motive : T -> Prop} (o_ctors : Vec (SCtor T) K) (k : Fin K) (base : RecCases motive o_ctors)
  : IotaCasesScaffolding1 (motive := motive) o_ctors k K o_ctors base
  := sorry
-- where go 

set_option pp.proofs true

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
  {base : RecCases motive ctors} -- we give it `recursor motive` as start!
  (body : (caseₖ : True) -> (base : RecCases motive ctors) -> Prop)
  : IotaCasesScaffolding1 (motive := motive) o_ctors k i ctors base -> Prop
| .thiscase ctors base =>
  let (ctor ::: ctors') := ctors
  (case : @RecCase T ctor ctor.spec ctor.ctor ctor.args id motive (RecCaseScaffold ctor)) ->
    IotaCases2 o_ctors recursor motive (body .intro case) ctors' (IotaCasesScaffold2 o_ctors k (base case))
| .before (i' := i') (ctors' := ctors') ctor base sub =>
  (case : @RecCase T ctor ctor.spec ctor.ctor ctor.args id motive (RecCaseScaffold ctor)) ->
    let smaller : IotaCasesScaffolding1 o_ctors k i' ctors' (base case) := sub case
    IotaCases1 (ctors := ctors') o_ctors recursor motive k (fun case'' base'' => sorry) sorry

-- def IotaArgsFairing
--   (ctors : Vec (SCtor T) K)
--   (recursor : Rec ctors)
--   (motive : T -> Prop)
--   (k : Fin K)
--   -- (taker : SCtorType T (Get ctors k).spec)
--   (body : T -> Prop)
--   : Prop
--   := sorry

-- This is about the args, so after cases.
-- def IotaAux 
--   (ctors : Vec (SCtor T) K)
--   (recursor : Rec ctors)
--   (motive : T -> Prop)
--   -- (k : Fin K)
--   (base : (t : T) -> motive t) -- or maybe this? `RecCases motive ctors ->`
--   -- (case : RecCase motive (Get ctors k).spec (Get ctors k).ctor (Get ctors k).args id)
--   -- (spec : SCtorSpec)
--   -- (ctor : SCtorType T spec)
--   :
--   (spec : SCtorSpec) ->
--   (ctor : SCtorType T spec) -> -- this is also our `t : T`, so the value we are eliminating (note that `SCtorType T []` ==β=> `T`).
--   (args : SCtorArgs T spec ctor) ->
--   (mots : Prop -> Prop) ->
--   (rhs : RecCase motive spec ctor args mots) ->
--   Prop
-- | .nil          , ctor, args, mots, rhs => base ctor = rhs
-- | .self    spec', ctor, args, mots, rhs =>
--   (arg : T) ->
--     IotaAux ctors recursor motive base spec' (ctor arg) sorry sorry (base arg)
-- | .other U spec', ctor, args, mots, rhs =>
--   (arg : U) ->
--     IotaAux ctors recursor motive base spec' (ctor arg) sorry sorry rhs

def Iota (ctors : Vec (SCtor T) K) (recursor : Rec ctors) (k : Fin K) : Prop :=
  (motive : T -> Prop) ->
    let xxx : RecCases motive ctors := recursor motive
    IotaCases1 ctors recursor motive k fun base case =>
      sorry
      -- IotaAux ctors recursor motive base case (Get ctors k).spec (Get ctors k).ctor
      -- IotaArgsFairing ctors recursor motive k fun t =>
      --   base t = sorry






namespace Test
  structure _SimpleInductiveType (T : Type) where
    K : Nat -- the amount of constructors
    ctors : Vec (SCtor T) K
    recursor : Rec ctors
    iotas : (k : Fin K) -> Iota ctors recursor k
end Test
