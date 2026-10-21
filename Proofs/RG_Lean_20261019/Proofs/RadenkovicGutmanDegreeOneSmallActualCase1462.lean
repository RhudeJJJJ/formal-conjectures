/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1462 : Family 9 := level9.get ⟨200,by decide⟩
def sourceMap1462 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1462 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1462_checked : acceptsGraphIso
    (source (graph core1462) (root 9) 0 1) DegreeOneSmallSpectrum1299.graph sourceMap1462=true := by decide +kernel
theorem fusedMap1462_checked : acceptsGraphIso
    (fused (graph core1462) (root 9) 0 1) DegreeOneSmallSpectrum1301.graph fusedMap1462=true := by decide +kernel
theorem certified1462 : Certified (graph core1462) (root 9) 0 1 :=
  of_native_maps core1462 DegreeOneSmallSpectrum1299.graph DegreeOneSmallSpectrum1301.graph
    sourceMap1462 fusedMap1462 sourceMap1462_checked fusedMap1462_checked
    DegreeOneSmallComparisons.comparison1462
#print axioms sourceMap1462_checked
#print axioms fusedMap1462_checked
#print axioms certified1462
def sourceMap1462swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1462swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1462swap_checked : acceptsGraphIso
    (source (graph core1462) (root 9) 1 0) DegreeOneSmallSpectrum1299.graph sourceMap1462swap=true := by decide +kernel
theorem fusedMap1462swap_checked : acceptsGraphIso
    (fused (graph core1462) (root 9) 1 0) DegreeOneSmallSpectrum1301.graph fusedMap1462swap=true := by decide +kernel
theorem certified1462swap : Certified (graph core1462) (root 9) 1 0 :=
  of_native_maps core1462 DegreeOneSmallSpectrum1299.graph DegreeOneSmallSpectrum1301.graph
    sourceMap1462swap fusedMap1462swap sourceMap1462swap_checked fusedMap1462swap_checked
    DegreeOneSmallComparisons.comparison1462
#print axioms sourceMap1462swap_checked
#print axioms fusedMap1462swap_checked
#print axioms certified1462swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
