
inductive Tree : Type where
| leaf : Tree
| node : Nat -> Tree -> Tree -> Tree

#check Tree.rec
/-
  {motive : Tree → Sort u} →
  motive Tree.leaf →
  ((a : Nat) → (a_1 a_2 : Tree) → motive a_1 → motive a_2 → motive (Tree.node a a_1 a_2)) →
  (t : Tree) →
  motive t
-/
