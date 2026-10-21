/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1532 : Family 9 := level9.get ⟨260,by decide⟩
def sourceMap1532 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1532 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1532_checked : acceptsGraphIso
    (source (graph core1532) (root 9) 0 1) DegreeOneSmallSpectrum1429.graph sourceMap1532=true := by decide +kernel
theorem fusedMap1532_checked : acceptsGraphIso
    (fused (graph core1532) (root 9) 0 1) DegreeOneSmallSpectrum1485.graph fusedMap1532=true := by decide +kernel
theorem certified1532 : Certified (graph core1532) (root 9) 0 1 :=
  of_native_maps core1532 DegreeOneSmallSpectrum1429.graph DegreeOneSmallSpectrum1485.graph
    sourceMap1532 fusedMap1532 sourceMap1532_checked fusedMap1532_checked
    DegreeOneSmallComparisons.comparison1532
#print axioms sourceMap1532_checked
#print axioms fusedMap1532_checked
#print axioms certified1532
def sourceMap1532swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1532swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1532swap_checked : acceptsGraphIso
    (source (graph core1532) (root 9) 1 0) DegreeOneSmallSpectrum1429.graph sourceMap1532swap=true := by decide +kernel
theorem fusedMap1532swap_checked : acceptsGraphIso
    (fused (graph core1532) (root 9) 1 0) DegreeOneSmallSpectrum1485.graph fusedMap1532swap=true := by decide +kernel
theorem certified1532swap : Certified (graph core1532) (root 9) 1 0 :=
  of_native_maps core1532 DegreeOneSmallSpectrum1429.graph DegreeOneSmallSpectrum1485.graph
    sourceMap1532swap fusedMap1532swap sourceMap1532swap_checked fusedMap1532swap_checked
    DegreeOneSmallComparisons.comparison1532
#print axioms sourceMap1532swap_checked
#print axioms fusedMap1532swap_checked
#print axioms certified1532swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
