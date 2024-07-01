import Aesop
import Reflection.Util.Vec

-- set_option pp.proofs true
set_option pp.fieldNotation.generalized false
-- set_option pp.universes true

@[simp, aesop unsafe]
theorem Sigma_rw_fst' {A B : Type u} (X : A -> Type u) (Y : B -> Type u)
  (h₁ : A = B) (h₂ : X = h₁ ▸ Y)
  : ((a : A) × X a) = ((b : B) × Y b)
  := by cases h₁; cases h₂; rfl

@[simp, aesop unsafe]
theorem Sigma_rw_fst {A B : Type u} (X : A -> Type u) (Y : B -> Type u) (h₁ : A = B)
  : ((a : A) × X a) = ((b : B) × X (h₁ ▸ b))
  := by cases h₁; rfl

@[simp, aesop safe]
theorem Sigma_rw_fst_val {A : Type u} {B : A -> Type v}
  (a₁ a₂ : A) (b₁ : B a₁) (b₂ : B a₂) (ha : a₁ = a₂) (hb : b₁ = ha ▸ b₂)
  : Sigma.mk a₁ b₁ = Sigma.mk a₂ b₂
  := by cases ha; cases hb; rfl

namespace Reflection.Util.Tele

/-
# Telescopes

We define the following inductive-recursive mutual block:
```
mutual
  inductive Tele : Nat -> Type
  | tnil : Tele 0
  | tcons : (tele : Tele n) -> (X : A tele -> Type) -> Tele (n+1)

  def f : Tele n -> Type
  | nil => Unit
  | cons tele X => (ts : f tele) × X ts
end
```
-/

-- private inductive Implementation.TList : Nat -> Type u -> Type (u+1)
-- | tnil : TList 0 PUnit
-- | next : (Ts : TList n TsR) -> (X : TsR -> Type u) -> TList (n+1) ((x : TsR) × X x)

/-- We reduce the ind-rec block above to this inductive type. -/
@[aesop unsafe constructors]
private inductive Implementation.TList : Type u -> Type (u+1)
| tnil : TList PUnit
| next : (Ts : TList TsR) -> (X : TsR -> Type u) -> TList ((x : TsR) × X x)
open Implementation

-- begin mutual block
def Tele : Type (u+1) := (TsR : Type u) × TList TsR

namespace Tele
  def A : Tele -> Type u
  | ⟨_, TList.tnil⟩ => PUnit
  | ⟨_, @TList.next TsR _ X⟩ => (x : TsR) × X x

  @[aesop unsafe] theorem th {Ts : Tele} : A Ts = Ts.fst := by
    let ⟨TsR, Ts⟩ := Ts
    induction Ts with
    | tnil => simp_all [A]
    | @next TsR _ X => simp_all [A]

  @[aesop unsafe] theorem th' {Ts : TList TsR} : A ⟨TsR, Ts⟩ = TsR := by rw [th]

  def tnil : Tele.{u} := ⟨PUnit.{u+1}, .tnil⟩
  def next (Ts : Tele.{u}) (X : A.{u} Ts -> Type _) : Tele.{u} := ⟨
    (x : A Ts) × X x,
    (Sigma_rw_fst X (th ▸ X) th) ▸ TList.next Ts.snd (fun x => X (th ▸ x))
  ⟩

  def recAux (motive : Tele.{u} -> Sort v)
    (case_nil : motive tnil)
    (case_next : (Ts : Tele.{u}) -> (X : A.{u} Ts -> Type u) -> motive Ts -> motive (next Ts X))
    : (TsR : Type u) -> (tlist : TList TsR) -> motive ⟨TsR, tlist⟩
  | .(PUnit), .tnil => case_nil
  | _, @TList.next TsR Ts X => by
    let tn : Tele := ⟨TsR, Ts⟩
    let ih := recAux motive case_nil case_next TsR Ts
    have :  next ⟨TsR, Ts⟩ (th ▸ X) = ⟨(x : TsR) × X x, TList.next Ts X⟩ := by
      rw [next, Sigma_rw_fst_val]
      aesop
      sorry -- just equality shifting
    exact this ▸ case_next ⟨TsR, Ts⟩ (th ▸ X) ih

  abbrev rec (motive : Tele.{u} -> Sort v)
    (case_nil : motive tnil)
    (case_next : (Ts : Tele.{u}) -> (X : A.{u} Ts -> Type u) -> motive Ts -> motive (next Ts X))
    : (t : Tele.{u}) -> motive t
  | ⟨TsR, tele⟩ => recAux motive case_nil case_next TsR tele


  @[simp] theorem iota_tnil : rec motive case_nil case_next (tnil) = case_nil := rfl
  @[simp] theorem iota_tcons : rec motive cnil ccons (next Ts X) = ccons Ts X (rec motive cnil ccons Ts) := by
    unfold rec recAux
    simp_all only
    aesop
end Tele
-- end mutual block

instance : CoeSort (Tele.{u}) (Type u) := ⟨Tele.A⟩

open Tele

@[simp] theorem A.nil : A tnil = PUnit := rfl
-- @[simp] theorem Tele.plusOne {tele : Tele (n+1)} : tele = next tele' X := by sorry
-- theorem A.next : A (next tele X) = ((x : A tele) × X x) := by sorry

def Has1 (tele : Tele) : Prop := ¬(tele = tnil)

/-- We know the first type in the telescope is always a full type `X : Unit -> Type _`, so we can read it. -/
def Head (tele : Tele.{u}) : Has1 tele -> Type u := sorry
  -- := @Tele.rec.{u} (@fun _tele => (m:Nat) -> m + 1 = n -> Type _) -- for a given `Tele n`
  --   (fun _ _ => by aesop)
  --   (@fun n (tele : Tele n) (X : A tele → Type u) (ih : (m : Nat) → m + 1 = n → Type u) m   _h =>
  --     match n with
  --     | 0 => (A.nil' ▸ X) ⟨⟩
  --     | n+1 => ih n rfl
  --   )
  --   (n+1)
  --   tele
  --   n
  --   rfl

theorem Head.next_same : Head (next tele X) sorry = Head tele h1 := sorry
  -- := by simp only [Head, Nat.reduceAdd, iota_tcons] -- wtf why is this proof so easy?
def Head.cast (val : Head (next tele X) sorry) : Head tele has1 := Head.next_same ▸ val

-- set_option pp.match false
-- @[simp] theorem A.one {tele : Tele.{u} 1} : A tele = ((x : PUnit) × Head tele) := by sorry
def tele1 : Tele := next tnil (fun _ => Nat)
def tele2 : Tele := next (next tnil (fun _ => Nat)) (fun ⟨(), n⟩ => Fin n) -- `[n:Nat, Fin n]`
#reduce A tnil
#reduce A tele1
#reduce A tele2
example : A tnil  =               PUnit                       := rfl
example : A tele1 = (        (_ : PUnit) × Nat              ) := rfl
example : A tele2 = ((vals : (_ : PUnit) × Nat) × Fin vals.2) := rfl
#check (_ : PUnit) × Fin 123 -- ≡ A (Tail tele2 123)

example : A tele2 := ⟨⟨⟨⟩, 10⟩, ⟨5, by omega⟩⟩



/-
def Tail : (n : Nat) -> (tele : Tele.{u} (n+1)) -> (a : Peek tele) -> Tele n
| 0  , next tnil X         , a => tnil
| n+1, next (next tele X) Y, a =>
  -- tele : Tele n
  -- X : A tele
  -- (next tele X) : Tele (n+1)
  -- Y : A (next tele X)
  -- a : Peek (next (next tele X) Y)

  let ih : Tele n := Tail n (next tele X) a.cast -- n is smaller, the telescope is smaller too.
  let res : Tele (n+1) := next ih
-/

def Tail (tele : Tele.{u}) {h1} (val : Head.{u} tele h1) : Tele.{u} := sorry
  -- := @Tele.rec.{u} (@fun n telee => (m:Nat) -> (h : n = m + 1) -> @Head m (h ▸ telee) -> Tele m) -- for a given `Tele n`
  --   (fun _ _ _ => by omega)
  --   (@fun n (tele : Tele n) (X : A tele → Type u) ih m hm a => by
  --     -- `tele ≡ [a:A, b:B a, c:C a b, ...] : Tele (m+1)`
  --     simp at hm
  --     cases hm
  --     simp at hm
  --     simp at ih
  --     match n with
  --     | 0 => -- `Tail [a:A] val   ≣   []`
  --       exact tnil
  --     | 1 =>

  --       sorry
  --     | n+1 => -- `Tail [a:A, b:B a, c:C a b, d: D a b c] val  ≣  [b:B val, c:B val b, c: C val b, d: D val b c]`
  --       -- `Tail [a:A, b:B a, c:C a b, d: D a b c] val   ≣   (Tail [a:A, b:B a, c:C a b] val) ++ [d:D val b c]`
  --       -- let tele_sub : Tele n := ih n rfl a.cast
  --       let asdf : Tele (n+1) := next
  --         (ih n rfl a.cast)
  --         (fun (bcd : A (ih n rfl a.cast)) => by -- `bcd ≡ ⟨⟨(), myfin⟩, mywhatever⟩`, where `a` is already baked in
  --           let a : Head tele := Head.next_same ▸ a
  --           -- a + bcd = abcd
  --           let abcd : A tele := sorry -- `abcd ≡ ⟨⟨⟨(), 123⟩, myfin⟩, mywhatever⟩`
  --           exact X abcd
  --         )
  --       exact asdf
  --   )
  --   (n+1)
  --   tele
  --   n
  --   rfl
  --   val

#check Head tele2
#reduce Head tele2
-- #check Tail tele2 (nat_lit 123)
-- #reduce Tail tele2 (nat_lit 123)
-- example : Tail tele2 (nat_lit 123) = tele1 := rfl -- no, bad!
-- example : Tail tele2 (nat_lit 123) = next tnil (fun _ => Fin 123) := rfl -- this is what we want


-- ! This is nonsensical, we can't even know how many binders we have until we know the values...
def First (p : Nat) (tele : Tele) : Tele := sorry
  -- := Tele.rec (@fun len _ => (n : Nat) -> len = n + p -> Tele p)
  --   (fun nn h => by have : p = 0 := (by omega); exact this ▸ tnil)
  --   (@fun len tele X ih nn _ => -- `tele : Tele len` is the rest. Once we hit `len = p`, we're good!
  --     match nn with
  --     | 0 =>
  --       have : p = len + 1 := by simp_all only [Nat.zero_add]
  --       this ▸ next tele X
  --     | nn+1 => ih nn (by omega)
  --   )
  --   tele
  --   n
  --   rfl


def applyPrefix (tele : Tele) (vals : A tele) : Tele := sorry
  -- := Tele.rec (@fun len tele => (p : Nat) -> (h : len = n + p) -> A (First p (h ▸ tele)) -> Tele n)
  --   (fun m h vals => have : n = 0 := (by omega); this ▸ tnil)
  --   (@fun len tele X ih p h vals => by
  --     match p with
  --     | 0 =>
  --       have : n = len + 1 := by aesop
  --       exact this ▸ next tele X
  --     | p+1 =>
  --       simp at ih
  --       have h' : len = n + p := by omega
  --       cases h'
  --       let vals : A (First (p + 1) (next tele X)) := vals
  --       let x := head vals
  --       -- let asdf := apply (takePrefix (p + 1) (next tele X)) x

  --       -- tele ≡ [n:Nat, Fin n]     : Tele 2
  --       -- vals ≡ [123, ⟨100, by..⟩] : A tele
  --       -- have : takePrefix (m + 1) (next tele X) = next := sorry
  --       let vals : A (First p tele) := sorry
  --       apply ih
  --       exact vals
  --       simp_all
  --   )
  --   tele
  --   p
  --   rfl
  --   vals

-- #check applyPrefix (n := 1) (p := 1) tele2 ⟨⟨⟩, fun () => 123⟩

def Tele.cast (h : n = n') (tele : Tele n) : Tele n' := h ▸ tele

namespace bad
  /-- Example for `Nat` is `U`, for `Vec` is `SPi Nat (fun n => U)`. -/
  inductive Tyₛ (k) (tele : Tele k) : (n p : Nat) -> (hk:k=n+p) -> (vals : A (First p (Tele.cast hk tele))) -> Type u
  | U : Tyₛ k tele 0 k (by simp) vals
  | SPi (hk : k = n + 1 + p)
    (vals : A (First p (Tele.cast hk tele)))
    -- (X : Head (applyPrefix (Tele.cast hk tele) vals))
    -- (X : Type )
    (sub : (x : X) -> False)
    : Tyₛ k tele (n+1) p hk vals

  /-
    ! But... `Tele` imposes a fixed amount of binders. And with `T -> Tyₛ` we can have a variable amount.
    ...so even with `Tele`, we won't be able to capture all possibilities.
  -/
end bad


inductive Tyₛ (tele : Tele) : (vals : A tele) -> Type u


#exit
