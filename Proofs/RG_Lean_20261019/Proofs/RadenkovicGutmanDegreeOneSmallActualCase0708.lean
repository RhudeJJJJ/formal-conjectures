/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0708 : Family 7 := level7.get ⟨73,by decide⟩
def sourceMap0708 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 0 3 v)
def fusedMap0708 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0708_checked : acceptsGraphIso
    (source (graph core0708) (root 7) 0 3) DegreeOneSmallSpectrum1114.graph sourceMap0708=true := by decide +kernel
theorem fusedMap0708_checked : acceptsGraphIso
    (fused (graph core0708) (root 7) 0 3) DegreeOneSmallSpectrum1118.graph fusedMap0708=true := by decide +kernel
theorem certified0708 : Certified (graph core0708) (root 7) 0 3 :=
  of_native_maps core0708 DegreeOneSmallSpectrum1114.graph DegreeOneSmallSpectrum1118.graph
    sourceMap0708 fusedMap0708 sourceMap0708_checked fusedMap0708_checked
    DegreeOneSmallComparisons.comparison0708
#print axioms sourceMap0708_checked
#print axioms fusedMap0708_checked
#print axioms certified0708
def sourceMap0708swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,8] (sourceLabel 7 3 0 v)
def fusedMap0708swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0708swap_checked : acceptsGraphIso
    (source (graph core0708) (root 7) 3 0) DegreeOneSmallSpectrum1114.graph sourceMap0708swap=true := by decide +kernel
theorem fusedMap0708swap_checked : acceptsGraphIso
    (fused (graph core0708) (root 7) 3 0) DegreeOneSmallSpectrum1118.graph fusedMap0708swap=true := by decide +kernel
theorem certified0708swap : Certified (graph core0708) (root 7) 3 0 :=
  of_native_maps core0708 DegreeOneSmallSpectrum1114.graph DegreeOneSmallSpectrum1118.graph
    sourceMap0708swap fusedMap0708swap sourceMap0708swap_checked fusedMap0708swap_checked
    DegreeOneSmallComparisons.comparison0708
#print axioms sourceMap0708swap_checked
#print axioms fusedMap0708swap_checked
#print axioms certified0708swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
