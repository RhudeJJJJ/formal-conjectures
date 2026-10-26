/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanOriginalDegreeOneSmall
import Proofs.RadenkovicGutmanOriginalDegreeOneMiddle
import Proofs.RadenkovicGutmanOriginalDegreeOneLarge
import Proofs.RadenkovicGutmanOriginalDegreeTwoThree
import Proofs.RadenkovicGutmanOriginalSmallGeFour
import Proofs.RadenkovicGutmanOriginalDegreeFourToFortyfive
import Proofs.RadenkovicGutmanOriginalDegreeGeFortysix
import Proofs.RadenkovicGutmanSubmissionStatement

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

theorem path_minimum (n : ℕ) (hn : 1≤n)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    SubmissionStatement.laplacianEnergy (pathGraph n) ≤
      SubmissionStatement.laplacianEnergy T :=
  SubmissionStatement.path_minimum_of_conclusion n T
    (complete_original_conclusion n hn T hT)

theorem path_equality (n : ℕ) (hn : 1≤n)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    SubmissionStatement.laplacianEnergy T =
        SubmissionStatement.laplacianEnergy (pathGraph n) ↔
      Nonempty (T ≃g pathGraph n) :=
  SubmissionStatement.path_equality_of_conclusion n T
    (complete_original_conclusion n hn T hT)

#check @complete_original_conclusion
#check @path_minimum
#check @path_equality
#print axioms original_inputs
#print axioms complete_original_conclusion
#print axioms path_minimum
#print axioms path_equality
end
end Gebendorfer.RadenkovicGutman.CompleteOriginalProof
