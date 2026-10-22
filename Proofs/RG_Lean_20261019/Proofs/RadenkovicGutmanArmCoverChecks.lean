/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFastArmCover

namespace Gebendorfer.RadenkovicGutman.FastArmCover

theorem leaf_of_checks (d : ℚ) (c₁ c₂ : Fin 5) (a b s₀ s₁ t₀ t₁ R : ℚ)
    (c : FastNestedCellData.Cell) (hc : FastNestedCellData.accepts d c₁ c₂ c=true)
    (hshape : FastRectangularCell.shape c a b s₀ s₁ t₀ t₁=true) (hR : R ≤ c.payment) :
    accepts d c₁ c₂ a b s₀ s₁ t₀ t₁ R (.leaf c)=true := by
  exact decide_eq_true ⟨hc,hshape,hR⟩

theorem first_of_checks (d : ℚ) (c₁ c₂ : Fin 5) (a b s₀ s₁ t₀ t₁ R m : ℚ)
    (l r : Cover) (hl : accepts d c₁ c₂ a b s₀ m t₀ t₁ R l=true)
    (hr : accepts d c₁ c₂ a b m s₁ t₀ t₁ R r=true) :
    accepts d c₁ c₂ a b s₀ s₁ t₀ t₁ R (.first m l r)=true := by
  simpa only [accepts,Bool.and_eq_true] using And.intro hl hr

theorem second_of_checks (d : ℚ) (c₁ c₂ : Fin 5) (a b s₀ s₁ t₀ t₁ R m : ℚ)
    (l r : Cover) (hl : accepts d c₁ c₂ a b s₀ s₁ t₀ m R l=true)
    (hr : accepts d c₁ c₂ a b s₀ s₁ m t₁ R r=true) :
    accepts d c₁ c₂ a b s₀ s₁ t₀ t₁ R (.second m l r)=true := by
  simpa only [accepts,Bool.and_eq_true] using And.intro hl hr

theorem cells_cons_checked (d : ℚ) (c₁ c₂ : Fin 5) (c : FastNestedCellData.Cell)
    (cs : List FastNestedCellData.Cell) (hc : FastNestedCellData.accepts d c₁ c₂ c=true)
    (hs : cs.all (FastNestedCellData.accepts d c₁ c₂)=true) :
    (c::cs).all (FastNestedCellData.accepts d c₁ c₂)=true := by
  simpa only [List.all_cons,Bool.and_eq_true] using And.intro hc hs

#print axioms leaf_of_checks
#print axioms first_of_checks
#print axioms second_of_checks
#print axioms cells_cons_checked
end Gebendorfer.RadenkovicGutman.FastArmCover
