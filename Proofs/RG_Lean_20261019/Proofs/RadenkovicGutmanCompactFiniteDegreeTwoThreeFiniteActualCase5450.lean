/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5450 : Family 7 := level7.get ⟨96,by decide⟩
def sourceMap5450 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,7,8,9,1,2,3,4,5,6] (sourceLabel 7 0 0 v)
def fusedMap5450 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,7,8,9,1,2,3,6,4,5] (fusedLabel 7 0 0 v)
theorem sourceMap5450_checked : acceptsGraphIso
    (source (graph core5450) (root 7) 0 0) SmallGeFourSpectrum017.graph sourceMap5450=true := by decide +kernel
theorem fusedMap5450_checked : acceptsGraphIso
    (fused (graph core5450) (root 7) 0 0) DegreeOneSmallSpectrum108.graph fusedMap5450=true := by decide +kernel
theorem certified5450 : Certified (graph core5450) (root 7) 0 0 :=
  of_native_maps core5450 SmallGeFourSpectrum017.graph DegreeOneSmallSpectrum108.graph
    sourceMap5450 fusedMap5450 sourceMap5450_checked fusedMap5450_checked
    DegreeTwoThreeFiniteComparisons.comparison5450
#print axioms sourceMap5450_checked
#print axioms fusedMap5450_checked
#print axioms certified5450
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
