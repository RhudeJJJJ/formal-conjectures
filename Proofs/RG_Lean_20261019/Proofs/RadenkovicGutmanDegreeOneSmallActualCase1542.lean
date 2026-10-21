/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1542 : Family 9 := level9.get ⟨270,by decide⟩
def sourceMap1542 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1542 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 0 1 v)
theorem sourceMap1542_checked : acceptsGraphIso
    (source (graph core1542) (root 9) 0 1) DegreeOneSmallSpectrum1412.graph sourceMap1542=true := by decide +kernel
theorem fusedMap1542_checked : acceptsGraphIso
    (fused (graph core1542) (root 9) 0 1) DegreeOneSmallSpectrum1500.graph fusedMap1542=true := by decide +kernel
theorem certified1542 : Certified (graph core1542) (root 9) 0 1 :=
  of_native_maps core1542 DegreeOneSmallSpectrum1412.graph DegreeOneSmallSpectrum1500.graph
    sourceMap1542 fusedMap1542 sourceMap1542_checked fusedMap1542_checked
    DegreeOneSmallComparisons.comparison1542
#print axioms sourceMap1542_checked
#print axioms fusedMap1542_checked
#print axioms certified1542
def sourceMap1542swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1542swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 1 0 v)
theorem sourceMap1542swap_checked : acceptsGraphIso
    (source (graph core1542) (root 9) 1 0) DegreeOneSmallSpectrum1412.graph sourceMap1542swap=true := by decide +kernel
theorem fusedMap1542swap_checked : acceptsGraphIso
    (fused (graph core1542) (root 9) 1 0) DegreeOneSmallSpectrum1500.graph fusedMap1542swap=true := by decide +kernel
theorem certified1542swap : Certified (graph core1542) (root 9) 1 0 :=
  of_native_maps core1542 DegreeOneSmallSpectrum1412.graph DegreeOneSmallSpectrum1500.graph
    sourceMap1542swap fusedMap1542swap sourceMap1542swap_checked fusedMap1542swap_checked
    DegreeOneSmallComparisons.comparison1542
#print axioms sourceMap1542swap_checked
#print axioms fusedMap1542swap_checked
#print axioms certified1542swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
