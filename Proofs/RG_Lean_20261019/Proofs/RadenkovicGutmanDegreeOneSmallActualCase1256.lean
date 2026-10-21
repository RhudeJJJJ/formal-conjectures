/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1256 : Family 9 := level9.get ⟨35,by decide⟩
def sourceMap1256 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1256 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (fusedLabel 9 0 1 v)
theorem sourceMap1256_checked : acceptsGraphIso
    (source (graph core1256) (root 9) 0 1) DegreeOneSmallSpectrum931.graph sourceMap1256=true := by decide +kernel
theorem fusedMap1256_checked : acceptsGraphIso
    (fused (graph core1256) (root 9) 0 1) DegreeOneSmallSpectrum978.graph fusedMap1256=true := by decide +kernel
theorem certified1256 : Certified (graph core1256) (root 9) 0 1 :=
  of_native_maps core1256 DegreeOneSmallSpectrum931.graph DegreeOneSmallSpectrum978.graph
    sourceMap1256 fusedMap1256 sourceMap1256_checked fusedMap1256_checked
    DegreeOneSmallComparisons.comparison1256
#print axioms sourceMap1256_checked
#print axioms fusedMap1256_checked
#print axioms certified1256
def sourceMap1256swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1256swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (fusedLabel 9 1 0 v)
theorem sourceMap1256swap_checked : acceptsGraphIso
    (source (graph core1256) (root 9) 1 0) DegreeOneSmallSpectrum931.graph sourceMap1256swap=true := by decide +kernel
theorem fusedMap1256swap_checked : acceptsGraphIso
    (fused (graph core1256) (root 9) 1 0) DegreeOneSmallSpectrum978.graph fusedMap1256swap=true := by decide +kernel
theorem certified1256swap : Certified (graph core1256) (root 9) 1 0 :=
  of_native_maps core1256 DegreeOneSmallSpectrum931.graph DegreeOneSmallSpectrum978.graph
    sourceMap1256swap fusedMap1256swap sourceMap1256swap_checked fusedMap1256swap_checked
    DegreeOneSmallComparisons.comparison1256
#print axioms sourceMap1256swap_checked
#print axioms fusedMap1256swap_checked
#print axioms certified1256swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
