import Reflection.Vec
import Reflection.Simple.Constructors
import Reflection.Simple.RecursorScaffolding

set_option pp.proofs true

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

namespace TheMinimizedVersion
  inductive Ret {α : Type} (k : Nat) : (i : Nat) -> (xs : Vec α i) -> Type 1
  | done (xs : Vec α (.succ k)) : Ret k (.succ k) xs -- note that k occurs twice here.
  | step : False -> Ret k (.succ i') (x ::: xs')

  -- works with `k : Fin K` too.
  def f (k : Nat) : (i : {i:Nat//i>k}) -> (xs : Vec α i) -> Ret k i xs
  | ⟨.succ i', hk⟩, x ::: (xs' : Vec α i') =>
    if h : i' = k then
      let whatweget  : Ret i' (Nat.succ i') (x ::: xs') := Ret.done (x ::: xs')
      let whatweneed : Ret k  (Nat.succ i') (x ::: xs') := h ▸ whatweget
      whatweneed
    else
      sorry -- Ret.step ...
end TheMinimizedVersion

/-- Doesn't do much, just skips some ctors before thiscase. -/
inductive IotaCasesScaffolding1 {motive : T -> Prop} (o_ctors : Vec (SCtor T) K) (k : Fin K)
  : (i : Nat) -> (ctors : Vec (SCtor T) i) -> Type 2
| thiscase (ctors : Vec (SCtor T) (.succ k)) : IotaCasesScaffolding1 o_ctors k (.succ k) ctors
| before
  (ctor : SCtor T)
  (ctors' : Vec (SCtor T) i')
  :
  (sub : (case : @RecCase T ctor _ _ _ id motive (RecCaseScaffold ctor))
          -> IotaCasesScaffolding1 o_ctors k i' ctors' /-(base case)-/)
    -> IotaCasesScaffolding1 o_ctors k (.succ i') (ctor ::: ctors') --(base)

/-- Build the scaffolding from K to k. -/
def IotaCasesScaffold1 {motive : T -> Prop} (o_ctors : Vec (SCtor T) K) (k : Fin K) --(base : RecCases motive o_ctors)
  : IotaCasesScaffolding1 (motive := motive) o_ctors k K o_ctors --base
  := go ⟨K, by simp [k.isLt]⟩ o_ctors -- start with all ctors and go until ctorₖ.
where
  go {motive : T -> Prop} {o_ctors : Vec (SCtor T) K} {k : Fin K}
  : (i : {i : Nat // i > k}) -> (ctors : Vec (SCtor T) i) -> IotaCasesScaffolding1 (motive := motive) o_ctors k i ctors
  | ⟨.succ i', hi'⟩, ctor ::: (ctors' : Vec (SCtor T) i') =>
    if h : i' = k.val then
      let whatweget
        := IotaCasesScaffolding1.thiscase (motive := motive) (o_ctors := o_ctors) (ctor ::: ctors')
      let whatweneed : IotaCasesScaffolding1 o_ctors k (Nat.succ i'   ) (ctor ::: ctors' )
        := sorry
      whatweneed
    else
      sorry

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
      @RecCase T ctorₖ ctorₖ.spec ctorₖ.ctor ctorₖ.args id motive (RecCaseScaffold ctorₖ) ->
      RecCases motive ⟦⟧ ->
      Prop
    ) ->
    Prop
| .thiscase ctors, body =>
  let (ctorₖ ::: ctors') := ctors
  (caseₖ : @RecCase T ctorₖ _ _ _ id motive (RecCaseScaffold ctorₖ)) ->
    IotaCases2 o_ctors recursor motive (body ctorₖ caseₖ) ctors' (IotaCasesScaffold2 o_ctors k (base caseₖ))
| .before (i' := i') ctor ctors' sub, body =>
  (case : @RecCase T ctor _ _ _ id motive (RecCaseScaffold ctor)) ->
    IotaCases1 (ctors := ctors') o_ctors recursor motive k (base case) (sub case) body

def Iota (ctors : Vec (SCtor T) K) (recursor : Rec ctors) (k : Fin K) : Prop :=
  (motive : T -> Prop) ->
    IotaCases1 ctors recursor motive k (recursor motive) (IotaCasesScaffold1 ctors k) fun ctorₖ baseₖ base =>
      True
      -- IotaArgs (fun recArg => base ...) fun t =>
      --   base t = caseₖ args

namespace Test
  structure _SimpleInductiveType (T : Type) where
    K : Nat -- the amount of constructors
    ctors : Vec (SCtor T) K
    recursor : Rec ctors
    iotas : (k : Fin K) -> Iota ctors recursor k

  instance : _SimpleInductiveType ListN := {
    ctors :=
      ⟨.nil                   , ListN.nil,  cNil⟩ :::
      ⟨.other Nat (.self .nil), ListN.cons, cCons⟩ ::: ⟦⟧
    recursor := @ListN.rec
    iotas := fun
    | 0 => @ListN.iota_nil
    | 1 => @ListN.iota_cons
  }

end Test
