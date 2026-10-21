/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0572 : Family 7 := level7.get ⟨27,by decide⟩
def sourceMap0572 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0572 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0572_checked : acceptsGraphIso
    (source (graph core0572) (root 7) 1 2) DegreeOneSmallSpectrum1034.graph sourceMap0572=true := by decide +kernel
theorem fusedMap0572_checked : acceptsGraphIso
    (fused (graph core0572) (root 7) 1 2) DegreeOneSmallSpectrum863.graph fusedMap0572=true := by decide +kernel
theorem certified0572 : Certified (graph core0572) (root 7) 1 2 :=
  of_native_maps core0572 DegreeOneSmallSpectrum1034.graph DegreeOneSmallSpectrum863.graph
    sourceMap0572 fusedMap0572 sourceMap0572_checked fusedMap0572_checked
    DegreeOneSmallComparisons.comparison0572
#print axioms sourceMap0572_checked
#print axioms fusedMap0572_checked
#print axioms certified0572
def sourceMap0572swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0572swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0572swap_checked : acceptsGraphIso
    (source (graph core0572) (root 7) 2 1) DegreeOneSmallSpectrum1034.graph sourceMap0572swap=true := by decide +kernel
theorem fusedMap0572swap_checked : acceptsGraphIso
    (fused (graph core0572) (root 7) 2 1) DegreeOneSmallSpectrum863.graph fusedMap0572swap=true := by decide +kernel
theorem certified0572swap : Certified (graph core0572) (root 7) 2 1 :=
  of_native_maps core0572 DegreeOneSmallSpectrum1034.graph DegreeOneSmallSpectrum863.graph
    sourceMap0572swap fusedMap0572swap sourceMap0572swap_checked fusedMap0572swap_checked
    DegreeOneSmallComparisons.comparison0572
#print axioms sourceMap0572swap_checked
#print axioms fusedMap0572swap_checked
#print axioms certified0572swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
