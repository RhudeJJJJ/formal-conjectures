/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1310 : Family 9 := level9.get ⟨74,by decide⟩
def sourceMap1310 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1310 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1310_checked : acceptsGraphIso
    (source (graph core1310) (root 9) 0 1) DegreeOneSmallSpectrum1360.graph sourceMap1310=true := by decide +kernel
theorem fusedMap1310_checked : acceptsGraphIso
    (fused (graph core1310) (root 9) 0 1) DegreeOneSmallSpectrum916.graph fusedMap1310=true := by decide +kernel
theorem certified1310 : Certified (graph core1310) (root 9) 0 1 :=
  of_native_maps core1310 DegreeOneSmallSpectrum1360.graph DegreeOneSmallSpectrum916.graph
    sourceMap1310 fusedMap1310 sourceMap1310_checked fusedMap1310_checked
    DegreeOneSmallComparisons.comparison1310
#print axioms sourceMap1310_checked
#print axioms fusedMap1310_checked
#print axioms certified1310
def sourceMap1310swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1310swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1310swap_checked : acceptsGraphIso
    (source (graph core1310) (root 9) 1 0) DegreeOneSmallSpectrum1360.graph sourceMap1310swap=true := by decide +kernel
theorem fusedMap1310swap_checked : acceptsGraphIso
    (fused (graph core1310) (root 9) 1 0) DegreeOneSmallSpectrum916.graph fusedMap1310swap=true := by decide +kernel
theorem certified1310swap : Certified (graph core1310) (root 9) 1 0 :=
  of_native_maps core1310 DegreeOneSmallSpectrum1360.graph DegreeOneSmallSpectrum916.graph
    sourceMap1310swap fusedMap1310swap sourceMap1310swap_checked fusedMap1310swap_checked
    DegreeOneSmallComparisons.comparison1310
#print axioms sourceMap1310swap_checked
#print axioms fusedMap1310swap_checked
#print axioms certified1310swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
