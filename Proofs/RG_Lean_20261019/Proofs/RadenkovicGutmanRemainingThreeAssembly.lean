/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanOriginalDegreeGeFortysix
import Proofs.RadenkovicGutmanOriginalSmallGeFour
import Proofs.RadenkovicGutmanOriginalDegreeOneSmall
import Proofs.RadenkovicGutmanOriginalDegreeOneLarge

/-! Assembly supplying four original Input families.
The three fields retain their original scope and remain explicit obligations. -/
namespace Gebendorfer.RadenkovicGutman.RemainingThreeAssembly
open SimpleGraph CoreQuotient ActualFusionIntegral OriginalAssembly GlobalAssembly
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

structure Inputs : Prop where
  degreeOneMiddle : ∀ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
    (source C u p q).IsTree → C.degree u=1 → 14≤order C p q → order C p q≤52 →
      0<meanIntegral C u p q
  degreeTwoThree : ∀ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
    (source C u p q).IsTree → (C.degree u=2 ∨ C.degree u=3) →
      0<meanIntegral C u p q
  degreeFourToFortyfive : ∀ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
    (source C u p q).IsTree → 4≤C.degree u → C.degree u≤45 → 13≤order C p q →
      2/13<normalizedIntegral C u p q 2

theorem degreeOneLarge (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : C.degree u=1) (hN : 53≤order C p q) :
    (189/5000 : ℝ)<normalizedIntegral C u p q 2 :=
  OriginalDegreeOneLarge.input_family m C u p q hT hd hN

theorem toOriginalInputs (h : Inputs) : OriginalAssembly.Inputs :=
  { degreeOneSmall := OriginalDegreeOneSmall.input_family
    degreeOneMiddle := h.degreeOneMiddle
    degreeOneLarge := degreeOneLarge
    degreeTwoThree := h.degreeTwoThree
    degreeGeFourSmall := OriginalSmallGeFour.input_family
    degreeFourToFortyfive := h.degreeFourToFortyfive
    degreeGeFortysix := OriginalDegreeGeFortysix.input_family }

theorem inputs_imply_uniform (h : Inputs) : SmallOrders.UniformStrictFusion :=
  OriginalAssembly.inputs_imply_uniform (toOriginalInputs h)

theorem universal_conclusion_of_remaining_inputs (h : Inputs) (n : ℕ) (hn : 1≤n)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree) : Conclusion T :=
  OriginalAssembly.universal_conclusion_of_original_inputs (toOriginalInputs h) n hn T hT

#print axioms degreeOneLarge
#print axioms toOriginalInputs
#print axioms inputs_imply_uniform
#print axioms universal_conclusion_of_remaining_inputs
end
end Gebendorfer.RadenkovicGutman.RemainingThreeAssembly

