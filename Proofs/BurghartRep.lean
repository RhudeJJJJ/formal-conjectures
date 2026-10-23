import Proofs.BurghartBase

/-! # BurghartRep
Exact-definition certificate for Burghart Conjecture 20.
All finite computations are checked by the Lean kernel. -/

namespace BurghartCertificate
def repOf (G : SimpleGraph (Fin 28)) [DecidableRel G.Adj]
    (d : Fin 28 → Fin 28 → ℕ) (C : Finset (Finset (Fin 28))) : BurghartReflection.Rep :=
  BurghartReflection.sum C fun S =>
    BurghartReflection.sum (boundaryCode G S) fun v =>
      BurghartReflection.sum (fringeCode (leavesCode G d) d v).powerset fun A =>
        if (pathsCode d v A).card = 0 then 0 else
          BurghartReflection.single (S.card,(boundaryCode G S).card - 1,(pathsCode d v A).card - 1)
            (-((-1:ℤ)^A.card))


end BurghartCertificate
