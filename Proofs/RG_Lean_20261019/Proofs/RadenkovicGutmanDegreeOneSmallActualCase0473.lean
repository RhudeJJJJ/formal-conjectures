/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0473 : Family 7 := level7.get ⟨4,by decide⟩
def sourceMap0473 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,5,2,3,4] (sourceLabel 7 0 2 v)
def fusedMap0473 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0473_checked : acceptsGraphIso
    (source (graph core0473) (root 7) 0 2) DegreeOneSmallSpectrum391.graph sourceMap0473=true := by decide +kernel
theorem fusedMap0473_checked : acceptsGraphIso
    (fused (graph core0473) (root 7) 0 2) DegreeOneSmallSpectrum396.graph fusedMap0473=true := by decide +kernel
theorem certified0473 : Certified (graph core0473) (root 7) 0 2 :=
  of_native_maps core0473 DegreeOneSmallSpectrum391.graph DegreeOneSmallSpectrum396.graph
    sourceMap0473 fusedMap0473 sourceMap0473_checked fusedMap0473_checked
    DegreeOneSmallComparisons.comparison0473
#print axioms sourceMap0473_checked
#print axioms fusedMap0473_checked
#print axioms certified0473
def sourceMap0473swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 7 2 0 v)
def fusedMap0473swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0473swap_checked : acceptsGraphIso
    (source (graph core0473) (root 7) 2 0) DegreeOneSmallSpectrum391.graph sourceMap0473swap=true := by decide +kernel
theorem fusedMap0473swap_checked : acceptsGraphIso
    (fused (graph core0473) (root 7) 2 0) DegreeOneSmallSpectrum396.graph fusedMap0473swap=true := by decide +kernel
theorem certified0473swap : Certified (graph core0473) (root 7) 2 0 :=
  of_native_maps core0473 DegreeOneSmallSpectrum391.graph DegreeOneSmallSpectrum396.graph
    sourceMap0473swap fusedMap0473swap sourceMap0473swap_checked fusedMap0473swap_checked
    DegreeOneSmallComparisons.comparison0473
#print axioms sourceMap0473swap_checked
#print axioms fusedMap0473swap_checked
#print axioms certified0473swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
