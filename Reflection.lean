import Reflection.Vec
-- import Reflection.Simple.Constructors
-- import Reflection.Simple.Recursor
-- import Reflection.Simple.Iotas
import Reflection.Simple.InductiveType
-- import Reflection.Simple.Expressions


def eraseIndices (T : Type) : SimpleInductiveType T -> ((Erased : Type) × (Guard : Erased -> Prop) × SimpleInductiveType Erased)
| ⟨.succ k, ⟨spec, c, hc⟩ ::: cs, recursor⟩ => sorry
| ⟨0, ⟦⟧, recursor⟩ => sorry

-- def translate (φ : Prop) : LeanPred φ -> ((φ' : Prop) × SimplePred φ')
-- | .inductive => eraseIndices
