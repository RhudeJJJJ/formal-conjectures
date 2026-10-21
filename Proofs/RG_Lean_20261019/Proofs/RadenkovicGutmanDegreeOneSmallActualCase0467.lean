/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0467 : Family 7 := level7.get ⟨3,by decide⟩
def sourceMap0467 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,5,2,3,4] (sourceLabel 7 0 2 v)
def fusedMap0467 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0467_checked : acceptsGraphIso
    (source (graph core0467) (root 7) 0 2) DegreeOneSmallSpectrum390.graph sourceMap0467=true := by decide +kernel
theorem fusedMap0467_checked : acceptsGraphIso
    (fused (graph core0467) (root 7) 0 2) DegreeOneSmallSpectrum392.graph fusedMap0467=true := by decide +kernel
theorem certified0467 : Certified (graph core0467) (root 7) 0 2 :=
  of_native_maps core0467 DegreeOneSmallSpectrum390.graph DegreeOneSmallSpectrum392.graph
    sourceMap0467 fusedMap0467 sourceMap0467_checked fusedMap0467_checked
    DegreeOneSmallComparisons.comparison0467
#print axioms sourceMap0467_checked
#print axioms fusedMap0467_checked
#print axioms certified0467
def sourceMap0467swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 7 2 0 v)
def fusedMap0467swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0467swap_checked : acceptsGraphIso
    (source (graph core0467) (root 7) 2 0) DegreeOneSmallSpectrum390.graph sourceMap0467swap=true := by decide +kernel
theorem fusedMap0467swap_checked : acceptsGraphIso
    (fused (graph core0467) (root 7) 2 0) DegreeOneSmallSpectrum392.graph fusedMap0467swap=true := by decide +kernel
theorem certified0467swap : Certified (graph core0467) (root 7) 2 0 :=
  of_native_maps core0467 DegreeOneSmallSpectrum390.graph DegreeOneSmallSpectrum392.graph
    sourceMap0467swap fusedMap0467swap sourceMap0467swap_checked fusedMap0467swap_checked
    DegreeOneSmallComparisons.comparison0467
#print axioms sourceMap0467swap_checked
#print axioms fusedMap0467swap_checked
#print axioms certified0467swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
