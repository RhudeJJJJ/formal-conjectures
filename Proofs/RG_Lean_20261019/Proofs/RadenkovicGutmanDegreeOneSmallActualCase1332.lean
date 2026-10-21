/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1332 : Family 9 := level9.get ⟨88,by decide⟩
def sourceMap1332 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1332 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (fusedLabel 9 0 1 v)
theorem sourceMap1332_checked : acceptsGraphIso
    (source (graph core1332) (root 9) 0 1) DegreeOneSmallSpectrum1410.graph sourceMap1332=true := by decide +kernel
theorem fusedMap1332_checked : acceptsGraphIso
    (fused (graph core1332) (root 9) 0 1) DegreeOneSmallSpectrum941.graph fusedMap1332=true := by decide +kernel
theorem certified1332 : Certified (graph core1332) (root 9) 0 1 :=
  of_native_maps core1332 DegreeOneSmallSpectrum1410.graph DegreeOneSmallSpectrum941.graph
    sourceMap1332 fusedMap1332 sourceMap1332_checked fusedMap1332_checked
    DegreeOneSmallComparisons.comparison1332
#print axioms sourceMap1332_checked
#print axioms fusedMap1332_checked
#print axioms certified1332
def sourceMap1332swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1332swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (fusedLabel 9 1 0 v)
theorem sourceMap1332swap_checked : acceptsGraphIso
    (source (graph core1332) (root 9) 1 0) DegreeOneSmallSpectrum1410.graph sourceMap1332swap=true := by decide +kernel
theorem fusedMap1332swap_checked : acceptsGraphIso
    (fused (graph core1332) (root 9) 1 0) DegreeOneSmallSpectrum941.graph fusedMap1332swap=true := by decide +kernel
theorem certified1332swap : Certified (graph core1332) (root 9) 1 0 :=
  of_native_maps core1332 DegreeOneSmallSpectrum1410.graph DegreeOneSmallSpectrum941.graph
    sourceMap1332swap fusedMap1332swap sourceMap1332swap_checked fusedMap1332swap_checked
    DegreeOneSmallComparisons.comparison1332
#print axioms sourceMap1332swap_checked
#print axioms fusedMap1332swap_checked
#print axioms certified1332swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
