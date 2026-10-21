/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0548 : Family 7 := level7.get ⟨19,by decide⟩
def sourceMap0548 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 7 1 2 v)
def fusedMap0548 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0548_checked : acceptsGraphIso
    (source (graph core0548) (root 7) 1 2) DegreeOneSmallSpectrum1489.graph sourceMap0548=true := by decide +kernel
theorem fusedMap0548_checked : acceptsGraphIso
    (fused (graph core0548) (root 7) 1 2) DegreeOneSmallSpectrum961.graph fusedMap0548=true := by decide +kernel
theorem certified0548 : Certified (graph core0548) (root 7) 1 2 :=
  of_native_maps core0548 DegreeOneSmallSpectrum1489.graph DegreeOneSmallSpectrum961.graph
    sourceMap0548 fusedMap0548 sourceMap0548_checked fusedMap0548_checked
    DegreeOneSmallComparisons.comparison0548
#print axioms sourceMap0548_checked
#print axioms fusedMap0548_checked
#print axioms certified0548
def sourceMap0548swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 7 2 1 v)
def fusedMap0548swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0548swap_checked : acceptsGraphIso
    (source (graph core0548) (root 7) 2 1) DegreeOneSmallSpectrum1489.graph sourceMap0548swap=true := by decide +kernel
theorem fusedMap0548swap_checked : acceptsGraphIso
    (fused (graph core0548) (root 7) 2 1) DegreeOneSmallSpectrum961.graph fusedMap0548swap=true := by decide +kernel
theorem certified0548swap : Certified (graph core0548) (root 7) 2 1 :=
  of_native_maps core0548 DegreeOneSmallSpectrum1489.graph DegreeOneSmallSpectrum961.graph
    sourceMap0548swap fusedMap0548swap sourceMap0548swap_checked fusedMap0548swap_checked
    DegreeOneSmallComparisons.comparison0548
#print axioms sourceMap0548swap_checked
#print axioms fusedMap0548swap_checked
#print axioms certified0548swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
