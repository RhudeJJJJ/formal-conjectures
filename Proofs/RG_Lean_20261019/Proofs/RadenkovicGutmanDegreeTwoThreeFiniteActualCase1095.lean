/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1095 : Family 7 := level7.get ⟨104,by decide⟩
def sourceMap1095 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 0 2 v)
def fusedMap1095 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap1095_checked : acceptsGraphIso
    (source (graph core1095) (root 7) 0 2) DegreeOneSmallSpectrum627.graph sourceMap1095=true := by decide +kernel
theorem fusedMap1095_checked : acceptsGraphIso
    (fused (graph core1095) (root 7) 0 2) DegreeOneSmallSpectrum630.graph fusedMap1095=true := by decide +kernel
theorem certified1095 : Certified (graph core1095) (root 7) 0 2 :=
  of_native_maps core1095 DegreeOneSmallSpectrum627.graph DegreeOneSmallSpectrum630.graph
    sourceMap1095 fusedMap1095 sourceMap1095_checked fusedMap1095_checked
    DegreeTwoThreeFiniteComparisons.comparison1095
#print axioms sourceMap1095_checked
#print axioms fusedMap1095_checked
#print axioms certified1095
def sourceMap1095swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,8] (sourceLabel 7 2 0 v)
def fusedMap1095swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap1095swap_checked : acceptsGraphIso
    (source (graph core1095) (root 7) 2 0) DegreeOneSmallSpectrum627.graph sourceMap1095swap=true := by decide +kernel
theorem fusedMap1095swap_checked : acceptsGraphIso
    (fused (graph core1095) (root 7) 2 0) DegreeOneSmallSpectrum630.graph fusedMap1095swap=true := by decide +kernel
theorem certified1095swap : Certified (graph core1095) (root 7) 2 0 :=
  of_native_maps core1095 DegreeOneSmallSpectrum627.graph DegreeOneSmallSpectrum630.graph
    sourceMap1095swap fusedMap1095swap sourceMap1095swap_checked fusedMap1095swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1095
#print axioms sourceMap1095swap_checked
#print axioms fusedMap1095swap_checked
#print axioms certified1095swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
