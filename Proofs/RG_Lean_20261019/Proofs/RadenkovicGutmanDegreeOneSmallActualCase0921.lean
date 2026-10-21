/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0921 : Family 8 := level8.get ⟨62,by decide⟩
def sourceMap0921 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0921 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0921_checked : acceptsGraphIso
    (source (graph core0921) (root 8) 0 2) DegreeOneSmallSpectrum1423.graph sourceMap0921=true := by decide +kernel
theorem fusedMap0921_checked : acceptsGraphIso
    (fused (graph core0921) (root 8) 0 2) DegreeOneSmallSpectrum924.graph fusedMap0921=true := by decide +kernel
theorem certified0921 : Certified (graph core0921) (root 8) 0 2 :=
  of_native_maps core0921 DegreeOneSmallSpectrum1423.graph DegreeOneSmallSpectrum924.graph
    sourceMap0921 fusedMap0921 sourceMap0921_checked fusedMap0921_checked
    DegreeOneSmallComparisons.comparison0921
#print axioms sourceMap0921_checked
#print axioms fusedMap0921_checked
#print axioms certified0921
def sourceMap0921swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0921swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0921swap_checked : acceptsGraphIso
    (source (graph core0921) (root 8) 2 0) DegreeOneSmallSpectrum1423.graph sourceMap0921swap=true := by decide +kernel
theorem fusedMap0921swap_checked : acceptsGraphIso
    (fused (graph core0921) (root 8) 2 0) DegreeOneSmallSpectrum924.graph fusedMap0921swap=true := by decide +kernel
theorem certified0921swap : Certified (graph core0921) (root 8) 2 0 :=
  of_native_maps core0921 DegreeOneSmallSpectrum1423.graph DegreeOneSmallSpectrum924.graph
    sourceMap0921swap fusedMap0921swap sourceMap0921swap_checked fusedMap0921swap_checked
    DegreeOneSmallComparisons.comparison0921
#print axioms sourceMap0921swap_checked
#print axioms fusedMap0921swap_checked
#print axioms certified0921swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
