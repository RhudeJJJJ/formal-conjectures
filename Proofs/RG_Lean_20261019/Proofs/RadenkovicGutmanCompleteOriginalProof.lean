/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanOriginalDegreeOneSmall
import Proofs.RadenkovicGutmanOriginalDegreeOneMiddle
import Proofs.RadenkovicGutmanOriginalDegreeOneLarge
import Proofs.RadenkovicGutmanOriginalDegreeTwoThree
import Proofs.RadenkovicGutmanOriginalSmallGeFour
import Proofs.RadenkovicGutmanOriginalDegreeFourToFortyfive
import Proofs.RadenkovicGutmanOriginalDegreeGeFortysix

/-! Concrete original seven-family conclusion. Completion and submission require
the successful kernel check of every imported family and of this endpoint. -/
namespace Gebendorfer.RadenkovicGutman.CompleteOriginalProof
open SimpleGraph GlobalAssembly
open scoped Classical
noncomputable section
theorem original_inputs : OriginalAssembly.Inputs :=
  { degreeOneSmall := OriginalDegreeOneSmall.input_family
    degreeOneMiddle := OriginalDegreeOneMiddle.input_family
    degreeOneLarge := OriginalDegreeOneLarge.input_family
    degreeTwoThree := OriginalDegreeTwoThree.input_family
    degreeGeFourSmall := OriginalSmallGeFour.input_family
    degreeFourToFortyfive := OriginalDegreeFourToFortyfive.input_family
    degreeGeFortysix := OriginalDegreeGeFortysix.input_family }
theorem complete_original_conclusion (n : ℕ) (hn : 1≤n)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree) : Conclusion T :=
  OriginalAssembly.universal_conclusion_of_original_inputs original_inputs n hn T hT
#check @complete_original_conclusion
#print axioms original_inputs
#print axioms complete_original_conclusion
end
end Gebendorfer.RadenkovicGutman.CompleteOriginalProof
