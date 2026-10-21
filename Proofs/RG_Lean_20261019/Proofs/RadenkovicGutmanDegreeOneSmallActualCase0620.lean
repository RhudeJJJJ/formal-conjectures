/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0620 : Family 7 := level7.get ⟨40,by decide⟩
def sourceMap0620 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0620 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0620_checked : acceptsGraphIso
    (source (graph core0620) (root 7) 1 2) DegreeOneSmallSpectrum1328.graph sourceMap0620=true := by decide +kernel
theorem fusedMap0620_checked : acceptsGraphIso
    (fused (graph core0620) (root 7) 1 2) DegreeOneSmallSpectrum910.graph fusedMap0620=true := by decide +kernel
theorem certified0620 : Certified (graph core0620) (root 7) 1 2 :=
  of_native_maps core0620 DegreeOneSmallSpectrum1328.graph DegreeOneSmallSpectrum910.graph
    sourceMap0620 fusedMap0620 sourceMap0620_checked fusedMap0620_checked
    DegreeOneSmallComparisons.comparison0620
#print axioms sourceMap0620_checked
#print axioms fusedMap0620_checked
#print axioms certified0620
def sourceMap0620swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0620swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0620swap_checked : acceptsGraphIso
    (source (graph core0620) (root 7) 2 1) DegreeOneSmallSpectrum1328.graph sourceMap0620swap=true := by decide +kernel
theorem fusedMap0620swap_checked : acceptsGraphIso
    (fused (graph core0620) (root 7) 2 1) DegreeOneSmallSpectrum910.graph fusedMap0620swap=true := by decide +kernel
theorem certified0620swap : Certified (graph core0620) (root 7) 2 1 :=
  of_native_maps core0620 DegreeOneSmallSpectrum1328.graph DegreeOneSmallSpectrum910.graph
    sourceMap0620swap fusedMap0620swap sourceMap0620swap_checked fusedMap0620swap_checked
    DegreeOneSmallComparisons.comparison0620
#print axioms sourceMap0620swap_checked
#print axioms fusedMap0620swap_checked
#print axioms certified0620swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
