/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFastRectangularCell

namespace Gebendorfer.RadenkovicGutman.FastArmCover
set_option maxHeartbeats 0

/-- Each branch divides the same physical arm parameter at one exact rational cut. -/
inductive Cover where
  | leaf : FastNestedCellData.Cell → Cover
  | first : ℚ → Cover → Cover → Cover
  | second : ℚ → Cover → Cover → Cover

def accepts (d : ℚ) (c₁ c₂ : Fin 5) (a b s₀ s₁ t₀ t₁ R : ℚ) : Cover → Bool
  | .leaf c => decide (FastNestedCellData.accepts d c₁ c₂ c=true ∧
      FastRectangularCell.shape c a b s₀ s₁ t₀ t₁=true ∧ R ≤ c.payment)
  | .first m l r => accepts d c₁ c₂ a b s₀ m t₀ t₁ R l &&
      accepts d c₁ c₂ a b m s₁ t₀ t₁ R r
  | .second m l r => accepts d c₁ c₂ a b s₀ s₁ t₀ m R l &&
      accepts d c₁ c₂ a b s₀ s₁ m t₁ R r

noncomputable section
theorem logarithm_lower (d : ℚ) (c₁ c₂ : Fin 5) (a b R : ℚ) (cover : Cover)
    (s₀ s₁ t₀ t₁ : ℚ) (h : accepts d c₁ c₂ a b s₀ s₁ t₀ t₁ R cover=true)
    (hd : 0 < (d : ℝ)) (y : ℝ) (hy : y ∈ Set.Icc (a : ℝ) (b : ℝ))
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hsrect : s ∈ Set.Icc (s₀ : ℝ) (s₁ : ℝ))
    (htrect : t ∈ Set.Icc (t₀ : ℝ) (t₁ : ℝ))
    (ζ : ℂ) (hζ : ‖ζ-Focus.g d y‖ ≤ Focus.r d y) :
    (R : ℝ) ≤ Real.log ‖Focus.quotient y
      (ArmClasses.parameter y c₁ s) (ArmClasses.parameter y c₂ t) ζ‖ := by
  induction cover generalizing s₀ s₁ t₀ t₁ with
  | leaf c =>
    obtain ⟨hc,hshape,hpaid⟩ := of_decide_eq_true h
    have hpay : (R : ℝ) ≤ c.payment := by exact_mod_cast hpaid
    exact hpay.trans (FastRectangularCell.logarithm_lower d c₁ c₂ c a b s₀ s₁ t₀ t₁
      hc hshape hd y hy s t hs ht hsrect htrect ζ hζ)
  | first m l r ihl ihr =>
    have hh : accepts d c₁ c₂ a b s₀ m t₀ t₁ R l=true ∧
        accepts d c₁ c₂ a b m s₁ t₀ t₁ R r=true := by
      simpa only [accepts,Bool.and_eq_true] using h
    rcases le_total s (m : ℝ) with hm | hm
    · exact ihl s₀ m t₀ t₁ hh.1 ⟨hsrect.1,hm⟩ htrect
    · exact ihr m s₁ t₀ t₁ hh.2 ⟨hm,hsrect.2⟩ htrect
  | second m l r ihl ihr =>
    have hh : accepts d c₁ c₂ a b s₀ s₁ t₀ m R l=true ∧
        accepts d c₁ c₂ a b s₀ s₁ m t₁ R r=true := by
      simpa only [accepts,Bool.and_eq_true] using h
    rcases le_total t (m : ℝ) with hm | hm
    · exact ihl s₀ s₁ t₀ m hh.1 hsrect ⟨htrect.1,hm⟩
    · exact ihr s₀ s₁ m t₁ hh.2 hsrect ⟨hm,htrect.2⟩

#print axioms logarithm_lower
end
end Gebendorfer.RadenkovicGutman.FastArmCover
