/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFactoredRoots

/-! A computable rational payment for the already sound complete root boxes.
This avoids repeating real-number simplification in every graph certificate.
Graph characteristic identities and complete root acceptance remain premises. -/
namespace Gebendorfer.RadenkovicGutman.RationalSpectralBounds
open FactoredRoots
set_option maxHeartbeats 0

def lowerQ (b : Box) (t : ℚ) : ℚ :=
  b.copies * ∑ i, max (b.lower i-t) 0
def upperQ (b : Box) (t : ℚ) : ℚ :=
  b.copies * ∑ i, max (b.upper i-t) 0
def lowerTotalQ : List Box → ℚ → ℚ
  | [], _ => 0
  | b::bs, t => lowerQ b t+lowerTotalQ bs t
def upperTotalQ : List Box → ℚ → ℚ
  | [], _ => 0
  | b::bs, t => upperQ b t+upperTotalQ bs t
def acceptsBounds (bs : List Box) (t l u : ℚ) : Bool :=
  decide (l ≤ lowerTotalQ bs t ∧ upperTotalQ bs t ≤ u)

theorem max_cast (a b : ℚ) : ((max a b : ℚ) : ℝ)=max (a : ℝ) (b : ℝ) := by
  by_cases h : a ≤ b
  · have hR : (a : ℝ) ≤ b := by exact_mod_cast h
    rw [max_eq_right h,max_eq_right hR]
  · have h' : b ≤ a := le_of_not_ge h
    have hR : (b : ℝ) ≤ a := by exact_mod_cast h'
    rw [max_eq_left h',max_eq_left hR]

theorem lowerQ_cast (b : Box) (t : ℚ) :
    (lowerQ b t : ℝ)=lower b (t : ℝ) := by
  simp [lowerQ,lower,max_cast]
theorem upperQ_cast (b : Box) (t : ℚ) :
    (upperQ b t : ℝ)=upper b (t : ℝ) := by
  simp [upperQ,upper,max_cast]
theorem lowerTotalQ_cast (bs : List Box) (t : ℚ) :
    (lowerTotalQ bs t : ℝ)=lowerTotal bs (t : ℝ) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change ((lowerQ b t+lowerTotalQ bs t : ℚ) : ℝ)=lower b (t : ℝ)+lowerTotal bs (t : ℝ)
    rw [Rat.cast_add,lowerQ_cast,ih]
theorem upperTotalQ_cast (bs : List Box) (t : ℚ) :
    (upperTotalQ bs t : ℝ)=upperTotal bs (t : ℝ) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change ((upperQ b t+upperTotalQ bs t : ℚ) : ℝ)=upper b (t : ℝ)+upperTotal bs (t : ℝ)
    rw [Rat.cast_add,upperQ_cast,ih]

open scoped Classical
noncomputable section
theorem graph_bounds {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (bs : List Box) (hb : allAccepted bs=true)
    (hp : (G.lapMatrix ℝ).charpoly=product bs) (t l u : ℚ)
    (hc : acceptsBounds bs t l u=true) :
    (l : ℝ) ≤ stopLoss (laplacianSpectrum G) (t : ℝ) ∧
      stopLoss (laplacianSpectrum G) (t : ℝ) ≤ (u : ℝ) := by
  have h := graph_stopLoss_bounds G bs hb hp (t : ℝ)
  have hl : (l : ℝ) ≤ (lowerTotalQ bs t : ℝ) := by
    exact_mod_cast (of_decide_eq_true hc).1
  have hu : (upperTotalQ bs t : ℝ) ≤ (u : ℝ) := by
    exact_mod_cast (of_decide_eq_true hc).2
  rw [lowerTotalQ_cast] at hl
  rw [upperTotalQ_cast] at hu
  exact ⟨hl.trans h.1,h.2.trans hu⟩
end

theorem repeated_control : acceptsBounds repeatedControl (1/2) (147/100) (153/100)=true := by
  decide +kernel
theorem inflated_lower_rejected : acceptsBounds repeatedControl (1/2) 2 3=false := by
  decide +kernel

#print axioms max_cast
#print axioms lowerQ_cast
#print axioms upperQ_cast
#print axioms lowerTotalQ_cast
#print axioms upperTotalQ_cast
#print axioms graph_bounds
#print axioms repeated_control
#print axioms inflated_lower_rejected
end Gebendorfer.RadenkovicGutman.RationalSpectralBounds
