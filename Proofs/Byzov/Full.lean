module

public import Proofs.Byzov.Group

/-! # Complete original Byzov--Pushkarev Conjecture 8

The exact original relation and the original augmentation shift action are
used. Every n>=2 is covered by the explicit bijective group homomorphism.
-/

@[expose] public section
namespace ByzovPushkarev

/-- Full original universal group-isomorphism statement, without extra hypotheses. -/
theorem full_conjecture8 (n : ℕ) (hn : 2 ≤ n) :
    Nonempty ((RelIso (adjacent n) (adjacent n)) ≃*
      (Multiplicative (ZMod 2) ×
        SemidirectProduct (Multiplicative (augmentation (orderParameter n)))
          (Multiplicative (Coord n)) (cyclicAction (orderParameter n)))) := by
  exact ⟨(MulEquiv.ofBijective (Certificate.targetHom n hn)
    ⟨Certificate.targetHom_injective n hn,Certificate.targetHom_surjective n hn⟩).symm⟩

end ByzovPushkarev
