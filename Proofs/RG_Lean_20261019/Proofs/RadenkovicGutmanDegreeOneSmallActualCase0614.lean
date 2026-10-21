/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0614 : Family 7 := level7.get ⟨39,by decide⟩
def sourceMap0614 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0614 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0614_checked : acceptsGraphIso
    (source (graph core0614) (root 7) 1 2) DegreeOneSmallSpectrum1310.graph sourceMap0614=true := by decide +kernel
theorem fusedMap0614_checked : acceptsGraphIso
    (fused (graph core0614) (root 7) 1 2) DegreeOneSmallSpectrum909.graph fusedMap0614=true := by decide +kernel
theorem certified0614 : Certified (graph core0614) (root 7) 1 2 :=
  of_native_maps core0614 DegreeOneSmallSpectrum1310.graph DegreeOneSmallSpectrum909.graph
    sourceMap0614 fusedMap0614 sourceMap0614_checked fusedMap0614_checked
    DegreeOneSmallComparisons.comparison0614
#print axioms sourceMap0614_checked
#print axioms fusedMap0614_checked
#print axioms certified0614
def sourceMap0614swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0614swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0614swap_checked : acceptsGraphIso
    (source (graph core0614) (root 7) 2 1) DegreeOneSmallSpectrum1310.graph sourceMap0614swap=true := by decide +kernel
theorem fusedMap0614swap_checked : acceptsGraphIso
    (fused (graph core0614) (root 7) 2 1) DegreeOneSmallSpectrum909.graph fusedMap0614swap=true := by decide +kernel
theorem certified0614swap : Certified (graph core0614) (root 7) 2 1 :=
  of_native_maps core0614 DegreeOneSmallSpectrum1310.graph DegreeOneSmallSpectrum909.graph
    sourceMap0614swap fusedMap0614swap sourceMap0614swap_checked fusedMap0614swap_checked
    DegreeOneSmallComparisons.comparison0614
#print axioms sourceMap0614swap_checked
#print axioms fusedMap0614swap_checked
#print axioms certified0614swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
