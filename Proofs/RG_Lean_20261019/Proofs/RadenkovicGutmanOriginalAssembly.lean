/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanClassEnvelope

/-!
# Exact assembly of the seven original certificate ranges

The seven fields below are unproved Lean certificate inputs. This module
checks their exhaustive composition, the physical order bounds and the
numeric cutoff payments. It does not promote stored Python witnesses to
kernel certificates. Source: unified manuscript revised 22 September 2026,
the coverage table and the final proof of the local transformation theorem.
-/
namespace Gebendorfer.RadenkovicGutman.OriginalAssembly
open SimpleGraph CoreQuotient ActualFusionIntegral GlobalAssembly
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev order {m : ℕ} (_C : SimpleGraph (Fin m)) (p q : ℕ) : ℕ :=
  Fintype.card (Fin m ⊕ Fin (p + 1) ⊕ Fin (q + 1))

abbrev meanIntegral {m : ℕ} (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ) : ℝ :=
  normalizedIntegral C u p q (2 - 2 / (order C p q : ℝ))

structure Inputs : Prop where
  degreeOneSmall : ∀ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
    (source C u p q).IsTree → C.degree u = 1 → order C p q ≤ 13 →
      0 < meanIntegral C u p q
  degreeOneMiddle : ∀ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
    (source C u p q).IsTree → C.degree u = 1 → 14 ≤ order C p q → order C p q ≤ 52 →
      0 < meanIntegral C u p q
  degreeOneLarge : ∀ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
    (source C u p q).IsTree → C.degree u = 1 → 53 ≤ order C p q →
      189 / 5000 < normalizedIntegral C u p q 2
  degreeTwoThree : ∀ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
    (source C u p q).IsTree → (C.degree u = 2 ∨ C.degree u = 3) →
      0 < meanIntegral C u p q
  degreeGeFourSmall : ∀ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
    (source C u p q).IsTree → 4 ≤ C.degree u → order C p q ≤ 12 →
      0 < meanIntegral C u p q
  degreeFourToFortyfive : ∀ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
    (source C u p q).IsTree → 4 ≤ C.degree u → C.degree u ≤ 45 → 13 ≤ order C p q →
      2 / 13 < normalizedIntegral C u p q 2
  degreeGeFortysix : ∀ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
    (source C u p q).IsTree → 46 ≤ C.degree u →
      2 / 47 < normalizedIntegral C u p q 2

theorem source_order_ge_degree_add_three {m : ℕ} (C : SimpleGraph (Fin m)) (u : Fin m)
    (p q : ℕ) : C.degree u + 3 ≤ order C p q := by
  have hd := C.degree_lt_card_verts u
  rw [Fintype.card_fin] at hd
  simp only [order, Fintype.card_sum, Fintype.card_fin]
  omega

theorem strict_of_cutoff_reserve {m : ℕ} (C : SimpleGraph (Fin m)) (u : Fin m) (p q K : ℕ)
    (hT : (source C u p q).IsTree) (hd : 1 ≤ C.degree u) (hK : 0 < K)
    (hn : K ≤ order C p q) (hr : 2 / (K : ℝ) < normalizedIntegral C u p q 2) :
    laplacianEnergy (fused C u p q) < laplacianEnergy (source C u p q) := by
  apply strict_of_reserve C u p q hT hd
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have hnr : (K : ℝ) ≤ order C p q := by exact_mod_cast hn
  have hnp : (0 : ℝ) < order C p q := lt_of_lt_of_le hk hnr
  have hle : (2 : ℝ) / (order C p q : ℝ) ≤ 2 / (K : ℝ) := by
    apply (div_le_div_iff₀ hnp hk).mpr
    nlinarith
  exact lt_of_le_of_lt hle hr

theorem inputs_imply_uniform (h : Inputs) : SmallOrders.UniformStrictFusion := by
  intro m C u p q hT hd
  by_cases h1 : C.degree u = 1
  · by_cases hn13 : order C p q ≤ 13
    · exact (strict_iff_mean_integral_pos C u p q hT hd).mpr
        (h.degreeOneSmall m C u p q hT h1 hn13)
    · by_cases hn52 : order C p q ≤ 52
      · exact (strict_iff_mean_integral_pos C u p q hT hd).mpr
          (h.degreeOneMiddle m C u p q hT h1 (by omega) hn52)
      · have hn53 : 53 ≤ order C p q := by omega
        apply strict_of_cutoff_reserve C u p q 53 hT hd (by omega) hn53
        exact lt_trans (by norm_num : (2 : ℝ) / 53 < 189 / 5000)
          (h.degreeOneLarge m C u p q hT h1 hn53)
  · by_cases h3 : C.degree u ≤ 3
    · exact (strict_iff_mean_integral_pos C u p q hT hd).mpr
        (h.degreeTwoThree m C u p q hT (by omega))
    · have h4 : 4 ≤ C.degree u := by omega
      by_cases hn12 : order C p q ≤ 12
      · exact (strict_iff_mean_integral_pos C u p q hT hd).mpr
          (h.degreeGeFourSmall m C u p q hT h4 hn12)
      · by_cases h45 : C.degree u ≤ 45
        · exact strict_of_cutoff_reserve C u p q 13 hT hd (by omega) (by omega)
            (h.degreeFourToFortyfive m C u p q hT h4 h45 (by omega))
        · have h46 : 46 ≤ C.degree u := by omega
          have hn := source_order_ge_degree_add_three C u p q
          exact strict_of_cutoff_reserve C u p q 47 hT hd (by omega) (by omega)
            (h.degreeGeFortysix m C u p q hT h46)

theorem universal_conclusion_of_original_inputs (h : Inputs) (n : ℕ) (hn : 1 ≤ n)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree) : Conclusion T :=
  OrderFour.universal_conclusion_of_strictFusion_five
    (MinimalFusion.uniformStrictFusion_iff_cutoff_five.mp (inputs_imply_uniform h)) n hn T hT

#check @Inputs
#check @inputs_imply_uniform
#check @universal_conclusion_of_original_inputs
#print axioms source_order_ge_degree_add_three
#print axioms strict_of_cutoff_reserve
#print axioms inputs_imply_uniform
#print axioms universal_conclusion_of_original_inputs
end
end Gebendorfer.RadenkovicGutman.OriginalAssembly
