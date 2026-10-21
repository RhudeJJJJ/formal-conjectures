/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1224 : Family 9 := level9.get ⟨16,by decide⟩
def sourceMap1224 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1224 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1224_checked : acceptsGraphIso
    (source (graph core1224) (root 9) 0 1) DegreeOneSmallSpectrum912.graph sourceMap1224=true := by decide +kernel
theorem fusedMap1224_checked : acceptsGraphIso
    (fused (graph core1224) (root 9) 0 1) DegreeOneSmallSpectrum915.graph fusedMap1224=true := by decide +kernel
theorem certified1224 : Certified (graph core1224) (root 9) 0 1 :=
  of_native_maps core1224 DegreeOneSmallSpectrum912.graph DegreeOneSmallSpectrum915.graph
    sourceMap1224 fusedMap1224 sourceMap1224_checked fusedMap1224_checked
    DegreeOneSmallComparisons.comparison1224
#print axioms sourceMap1224_checked
#print axioms fusedMap1224_checked
#print axioms certified1224
def sourceMap1224swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1224swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1224swap_checked : acceptsGraphIso
    (source (graph core1224) (root 9) 1 0) DegreeOneSmallSpectrum912.graph sourceMap1224swap=true := by decide +kernel
theorem fusedMap1224swap_checked : acceptsGraphIso
    (fused (graph core1224) (root 9) 1 0) DegreeOneSmallSpectrum915.graph fusedMap1224swap=true := by decide +kernel
theorem certified1224swap : Certified (graph core1224) (root 9) 1 0 :=
  of_native_maps core1224 DegreeOneSmallSpectrum912.graph DegreeOneSmallSpectrum915.graph
    sourceMap1224swap fusedMap1224swap sourceMap1224swap_checked fusedMap1224swap_checked
    DegreeOneSmallComparisons.comparison1224
#print axioms sourceMap1224swap_checked
#print axioms fusedMap1224swap_checked
#print axioms certified1224swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
