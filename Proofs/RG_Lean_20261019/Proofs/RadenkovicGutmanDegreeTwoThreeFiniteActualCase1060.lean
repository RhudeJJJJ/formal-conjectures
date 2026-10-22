/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1060 : Family 7 := level7.get ⟨11,by decide⟩
def sourceMap1060 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 7 0 2 v)
def fusedMap1060 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,11,7,8,9,10] (fusedLabel 7 0 2 v)
theorem sourceMap1060_checked : acceptsGraphIso
    (source (graph core1060) (root 7) 0 2) DegreeOneSmallSpectrum496.graph sourceMap1060=true := by decide +kernel
theorem fusedMap1060_checked : acceptsGraphIso
    (fused (graph core1060) (root 7) 0 2) DegreeOneSmallSpectrum377.graph fusedMap1060=true := by decide +kernel
theorem certified1060 : Certified (graph core1060) (root 7) 0 2 :=
  of_native_maps core1060 DegreeOneSmallSpectrum496.graph DegreeOneSmallSpectrum377.graph
    sourceMap1060 fusedMap1060 sourceMap1060_checked fusedMap1060_checked
    DegreeTwoThreeFiniteComparisons.comparison1060
#print axioms sourceMap1060_checked
#print axioms fusedMap1060_checked
#print axioms certified1060
def sourceMap1060swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9,11] (sourceLabel 7 2 0 v)
def fusedMap1060swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,11,7,8,9,10] (fusedLabel 7 2 0 v)
theorem sourceMap1060swap_checked : acceptsGraphIso
    (source (graph core1060) (root 7) 2 0) DegreeOneSmallSpectrum496.graph sourceMap1060swap=true := by decide +kernel
theorem fusedMap1060swap_checked : acceptsGraphIso
    (fused (graph core1060) (root 7) 2 0) DegreeOneSmallSpectrum377.graph fusedMap1060swap=true := by decide +kernel
theorem certified1060swap : Certified (graph core1060) (root 7) 2 0 :=
  of_native_maps core1060 DegreeOneSmallSpectrum496.graph DegreeOneSmallSpectrum377.graph
    sourceMap1060swap fusedMap1060swap sourceMap1060swap_checked fusedMap1060swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1060
#print axioms sourceMap1060swap_checked
#print axioms fusedMap1060swap_checked
#print axioms certified1060swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
