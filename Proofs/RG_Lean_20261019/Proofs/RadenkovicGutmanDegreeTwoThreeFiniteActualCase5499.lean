/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5499 : Family 6 := level6.get ⟨26,by decide⟩
def sourceMap5499 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,11,12,5,6,7,8,9,10] (sourceLabel 6 2 2 v)
def fusedMap5499 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap5499_checked : acceptsGraphIso
    (source (graph core5499) (root 6) 2 2) DegreeOneSmallSpectrum1877.graph sourceMap5499=true := by decide +kernel
theorem fusedMap5499_checked : acceptsGraphIso
    (fused (graph core5499) (root 6) 2 2) DegreeOneSmallSpectrum881.graph fusedMap5499=true := by decide +kernel
theorem certified5499 : Certified (graph core5499) (root 6) 2 2 :=
  of_native_maps core5499 DegreeOneSmallSpectrum1877.graph DegreeOneSmallSpectrum881.graph
    sourceMap5499 fusedMap5499 sourceMap5499_checked fusedMap5499_checked
    DegreeTwoThreeFiniteComparisons.comparison5499
#print axioms sourceMap5499_checked
#print axioms fusedMap5499_checked
#print axioms certified5499
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
