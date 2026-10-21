/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0564 : Family 7 := level7.get ⟨26,by decide⟩
def sourceMap0564 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0564 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0564_checked : acceptsGraphIso
    (source (graph core0564) (root 7) 0 3) DegreeOneSmallSpectrum1008.graph sourceMap0564=true := by decide +kernel
theorem fusedMap0564_checked : acceptsGraphIso
    (fused (graph core0564) (root 7) 0 3) DegreeOneSmallSpectrum862.graph fusedMap0564=true := by decide +kernel
theorem certified0564 : Certified (graph core0564) (root 7) 0 3 :=
  of_native_maps core0564 DegreeOneSmallSpectrum1008.graph DegreeOneSmallSpectrum862.graph
    sourceMap0564 fusedMap0564 sourceMap0564_checked fusedMap0564_checked
    DegreeOneSmallComparisons.comparison0564
#print axioms sourceMap0564_checked
#print axioms fusedMap0564_checked
#print axioms certified0564
def sourceMap0564swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0564swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0564swap_checked : acceptsGraphIso
    (source (graph core0564) (root 7) 3 0) DegreeOneSmallSpectrum1008.graph sourceMap0564swap=true := by decide +kernel
theorem fusedMap0564swap_checked : acceptsGraphIso
    (fused (graph core0564) (root 7) 3 0) DegreeOneSmallSpectrum862.graph fusedMap0564swap=true := by decide +kernel
theorem certified0564swap : Certified (graph core0564) (root 7) 3 0 :=
  of_native_maps core0564 DegreeOneSmallSpectrum1008.graph DegreeOneSmallSpectrum862.graph
    sourceMap0564swap fusedMap0564swap sourceMap0564swap_checked fusedMap0564swap_checked
    DegreeOneSmallComparisons.comparison0564
#print axioms sourceMap0564swap_checked
#print axioms fusedMap0564swap_checked
#print axioms certified0564swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
