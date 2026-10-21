/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0817 : Family 8 := level8.get ⟨23,by decide⟩
def sourceMap0817 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,5,2,3,4] (sourceLabel 8 0 2 v)
def fusedMap0817 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap0817_checked : acceptsGraphIso
    (source (graph core0817) (root 8) 0 2) DegreeOneSmallSpectrum959.graph sourceMap0817=true := by decide +kernel
theorem fusedMap0817_checked : acceptsGraphIso
    (fused (graph core0817) (root 8) 0 2) DegreeOneSmallSpectrum966.graph fusedMap0817=true := by decide +kernel
theorem certified0817 : Certified (graph core0817) (root 8) 0 2 :=
  of_native_maps core0817 DegreeOneSmallSpectrum959.graph DegreeOneSmallSpectrum966.graph
    sourceMap0817 fusedMap0817 sourceMap0817_checked fusedMap0817_checked
    DegreeOneSmallComparisons.comparison0817
#print axioms sourceMap0817_checked
#print axioms fusedMap0817_checked
#print axioms certified0817
def sourceMap0817swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (sourceLabel 8 2 0 v)
def fusedMap0817swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap0817swap_checked : acceptsGraphIso
    (source (graph core0817) (root 8) 2 0) DegreeOneSmallSpectrum959.graph sourceMap0817swap=true := by decide +kernel
theorem fusedMap0817swap_checked : acceptsGraphIso
    (fused (graph core0817) (root 8) 2 0) DegreeOneSmallSpectrum966.graph fusedMap0817swap=true := by decide +kernel
theorem certified0817swap : Certified (graph core0817) (root 8) 2 0 :=
  of_native_maps core0817 DegreeOneSmallSpectrum959.graph DegreeOneSmallSpectrum966.graph
    sourceMap0817swap fusedMap0817swap sourceMap0817swap_checked fusedMap0817swap_checked
    DegreeOneSmallComparisons.comparison0817
#print axioms sourceMap0817swap_checked
#print axioms fusedMap0817swap_checked
#print axioms certified0817swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
