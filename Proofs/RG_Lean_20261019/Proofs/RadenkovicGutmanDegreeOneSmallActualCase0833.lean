/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0833 : Family 8 := level8.get ⟨29,by decide⟩
def sourceMap0833 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,6,7,5,2,3,4] (sourceLabel 8 0 2 v)
def fusedMap0833 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 8 0 2 v)
theorem sourceMap0833_checked : acceptsGraphIso
    (source (graph core0833) (root 8) 0 2) DegreeOneSmallSpectrum957.graph sourceMap0833=true := by decide +kernel
theorem fusedMap0833_checked : acceptsGraphIso
    (fused (graph core0833) (root 8) 0 2) DegreeOneSmallSpectrum977.graph fusedMap0833=true := by decide +kernel
theorem certified0833 : Certified (graph core0833) (root 8) 0 2 :=
  of_native_maps core0833 DegreeOneSmallSpectrum957.graph DegreeOneSmallSpectrum977.graph
    sourceMap0833 fusedMap0833 sourceMap0833_checked fusedMap0833_checked
    DegreeOneSmallComparisons.comparison0833
#print axioms sourceMap0833_checked
#print axioms fusedMap0833_checked
#print axioms certified0833
def sourceMap0833swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,6,7,2,3,4,5] (sourceLabel 8 2 0 v)
def fusedMap0833swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 8 2 0 v)
theorem sourceMap0833swap_checked : acceptsGraphIso
    (source (graph core0833) (root 8) 2 0) DegreeOneSmallSpectrum957.graph sourceMap0833swap=true := by decide +kernel
theorem fusedMap0833swap_checked : acceptsGraphIso
    (fused (graph core0833) (root 8) 2 0) DegreeOneSmallSpectrum977.graph fusedMap0833swap=true := by decide +kernel
theorem certified0833swap : Certified (graph core0833) (root 8) 2 0 :=
  of_native_maps core0833 DegreeOneSmallSpectrum957.graph DegreeOneSmallSpectrum977.graph
    sourceMap0833swap fusedMap0833swap sourceMap0833swap_checked fusedMap0833swap_checked
    DegreeOneSmallComparisons.comparison0833
#print axioms sourceMap0833swap_checked
#print axioms fusedMap0833swap_checked
#print axioms certified0833swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
