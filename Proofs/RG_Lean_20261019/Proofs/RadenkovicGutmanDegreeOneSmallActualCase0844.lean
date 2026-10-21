/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0844 : Family 8 := level8.get ⟨35,by decide⟩
def sourceMap0844 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap0844 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0844_checked : acceptsGraphIso
    (source (graph core0844) (root 8) 0 1) DegreeOneSmallSpectrum409.graph sourceMap0844=true := by decide +kernel
theorem fusedMap0844_checked : acceptsGraphIso
    (fused (graph core0844) (root 8) 0 1) DegreeOneSmallSpectrum411.graph fusedMap0844=true := by decide +kernel
theorem certified0844 : Certified (graph core0844) (root 8) 0 1 :=
  of_native_maps core0844 DegreeOneSmallSpectrum409.graph DegreeOneSmallSpectrum411.graph
    sourceMap0844 fusedMap0844 sourceMap0844_checked fusedMap0844_checked
    DegreeOneSmallComparisons.comparison0844
#print axioms sourceMap0844_checked
#print axioms fusedMap0844_checked
#print axioms certified0844
def sourceMap0844swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap0844swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0844swap_checked : acceptsGraphIso
    (source (graph core0844) (root 8) 1 0) DegreeOneSmallSpectrum409.graph sourceMap0844swap=true := by decide +kernel
theorem fusedMap0844swap_checked : acceptsGraphIso
    (fused (graph core0844) (root 8) 1 0) DegreeOneSmallSpectrum411.graph fusedMap0844swap=true := by decide +kernel
theorem certified0844swap : Certified (graph core0844) (root 8) 1 0 :=
  of_native_maps core0844 DegreeOneSmallSpectrum409.graph DegreeOneSmallSpectrum411.graph
    sourceMap0844swap fusedMap0844swap sourceMap0844swap_checked fusedMap0844swap_checked
    DegreeOneSmallComparisons.comparison0844
#print axioms sourceMap0844swap_checked
#print axioms fusedMap0844swap_checked
#print axioms certified0844swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
