import Lean

open Lean PrettyPrinter Delaborator SubExpr Parser

-- Thanks Arthur https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Infoview.20notation/near/399047473

def unexpandStructs : Syntax → Delab
  | `({ $[ $_ := $fields],* $_? }) => `(⟨$[$fields],*⟩ )
  | `($s) => `($s)

@[delab app]
def delabApp : Delab := do unexpandStructs $ ← delabAppImplicit

-- To test:
-- def foo : Fin 2 := ⟨1, sorry⟩
-- #print foo