/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1107 : Family 8 := level8.get ⟨51,by decide⟩
def sourceMap1107 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 8 0 2 v)
def fusedMap1107 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (fusedLabel 8 0 2 v)
theorem sourceMap1107_checked : acceptsGraphIso
    (source (graph core1107) (root 8) 0 2) DegreeOneSmallSpectrum1281.graph sourceMap1107=true := by decide +kernel
theorem fusedMap1107_checked : acceptsGraphIso
    (fused (graph core1107) (root 8) 0 2) DegreeOneSmallSpectrum905.graph fusedMap1107=true := by decide +kernel
theorem certified1107 : Certified (graph core1107) (root 8) 0 2 :=
  of_native_maps core1107 DegreeOneSmallSpectrum1281.graph DegreeOneSmallSpectrum905.graph
    sourceMap1107 fusedMap1107 sourceMap1107_checked fusedMap1107_checked
    DegreeTwoThreeFiniteComparisons.comparison1107
#print axioms sourceMap1107_checked
#print axioms fusedMap1107_checked
#print axioms certified1107
def sourceMap1107swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9,12] (sourceLabel 8 2 0 v)
def fusedMap1107swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (fusedLabel 8 2 0 v)
theorem sourceMap1107swap_checked : acceptsGraphIso
    (source (graph core1107) (root 8) 2 0) DegreeOneSmallSpectrum1281.graph sourceMap1107swap=true := by decide +kernel
theorem fusedMap1107swap_checked : acceptsGraphIso
    (fused (graph core1107) (root 8) 2 0) DegreeOneSmallSpectrum905.graph fusedMap1107swap=true := by decide +kernel
theorem certified1107swap : Certified (graph core1107) (root 8) 2 0 :=
  of_native_maps core1107 DegreeOneSmallSpectrum1281.graph DegreeOneSmallSpectrum905.graph
    sourceMap1107swap fusedMap1107swap sourceMap1107swap_checked fusedMap1107swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1107
#print axioms sourceMap1107swap_checked
#print axioms fusedMap1107swap_checked
#print axioms certified1107swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
