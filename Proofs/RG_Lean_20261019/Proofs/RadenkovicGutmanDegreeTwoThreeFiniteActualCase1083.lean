/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1083 : Family 7 := level7.get ⟨75,by decide⟩
def sourceMap1083 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,9,10,11,6,7,8] (sourceLabel 7 0 2 v)
def fusedMap1083 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap1083_checked : acceptsGraphIso
    (source (graph core1083) (root 7) 0 2) DegreeOneSmallSpectrum743.graph sourceMap1083=true := by decide +kernel
theorem fusedMap1083_checked : acceptsGraphIso
    (fused (graph core1083) (root 7) 0 2) DegreeOneSmallSpectrum441.graph fusedMap1083=true := by decide +kernel
theorem certified1083 : Certified (graph core1083) (root 7) 0 2 :=
  of_native_maps core1083 DegreeOneSmallSpectrum743.graph DegreeOneSmallSpectrum441.graph
    sourceMap1083 fusedMap1083 sourceMap1083_checked fusedMap1083_checked
    DegreeTwoThreeFiniteComparisons.comparison1083
#print axioms sourceMap1083_checked
#print axioms fusedMap1083_checked
#print axioms certified1083
def sourceMap1083swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,9,10,6,7,8,11] (sourceLabel 7 2 0 v)
def fusedMap1083swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap1083swap_checked : acceptsGraphIso
    (source (graph core1083) (root 7) 2 0) DegreeOneSmallSpectrum743.graph sourceMap1083swap=true := by decide +kernel
theorem fusedMap1083swap_checked : acceptsGraphIso
    (fused (graph core1083) (root 7) 2 0) DegreeOneSmallSpectrum441.graph fusedMap1083swap=true := by decide +kernel
theorem certified1083swap : Certified (graph core1083) (root 7) 2 0 :=
  of_native_maps core1083 DegreeOneSmallSpectrum743.graph DegreeOneSmallSpectrum441.graph
    sourceMap1083swap fusedMap1083swap sourceMap1083swap_checked fusedMap1083swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1083
#print axioms sourceMap1083swap_checked
#print axioms fusedMap1083swap_checked
#print axioms certified1083swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
