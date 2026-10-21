/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1582 : Family 9 := level9.get ⟨323,by decide⟩
def sourceMap1582 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1582 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1582_checked : acceptsGraphIso
    (source (graph core1582) (root 9) 0 1) DegreeOneSmallSpectrum1583.graph sourceMap1582=true := by decide +kernel
theorem fusedMap1582_checked : acceptsGraphIso
    (fused (graph core1582) (root 9) 0 1) DegreeOneSmallSpectrum988.graph fusedMap1582=true := by decide +kernel
theorem certified1582 : Certified (graph core1582) (root 9) 0 1 :=
  of_native_maps core1582 DegreeOneSmallSpectrum1583.graph DegreeOneSmallSpectrum988.graph
    sourceMap1582 fusedMap1582 sourceMap1582_checked fusedMap1582_checked
    DegreeOneSmallComparisons.comparison1582
#print axioms sourceMap1582_checked
#print axioms fusedMap1582_checked
#print axioms certified1582
def sourceMap1582swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1582swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1582swap_checked : acceptsGraphIso
    (source (graph core1582) (root 9) 1 0) DegreeOneSmallSpectrum1583.graph sourceMap1582swap=true := by decide +kernel
theorem fusedMap1582swap_checked : acceptsGraphIso
    (fused (graph core1582) (root 9) 1 0) DegreeOneSmallSpectrum988.graph fusedMap1582swap=true := by decide +kernel
theorem certified1582swap : Certified (graph core1582) (root 9) 1 0 :=
  of_native_maps core1582 DegreeOneSmallSpectrum1583.graph DegreeOneSmallSpectrum988.graph
    sourceMap1582swap fusedMap1582swap sourceMap1582swap_checked fusedMap1582swap_checked
    DegreeOneSmallComparisons.comparison1582
#print axioms sourceMap1582swap_checked
#print axioms fusedMap1582swap_checked
#print axioms certified1582swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
