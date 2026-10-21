/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0606 : Family 7 := level7.get ⟨35,by decide⟩
def sourceMap0606 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0606 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0606_checked : acceptsGraphIso
    (source (graph core0606) (root 7) 0 3) DegreeOneSmallSpectrum1226.graph sourceMap0606=true := by decide +kernel
theorem fusedMap0606_checked : acceptsGraphIso
    (fused (graph core0606) (root 7) 0 3) DegreeOneSmallSpectrum881.graph fusedMap0606=true := by decide +kernel
theorem certified0606 : Certified (graph core0606) (root 7) 0 3 :=
  of_native_maps core0606 DegreeOneSmallSpectrum1226.graph DegreeOneSmallSpectrum881.graph
    sourceMap0606 fusedMap0606 sourceMap0606_checked fusedMap0606_checked
    DegreeOneSmallComparisons.comparison0606
#print axioms sourceMap0606_checked
#print axioms fusedMap0606_checked
#print axioms certified0606
def sourceMap0606swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0606swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0606swap_checked : acceptsGraphIso
    (source (graph core0606) (root 7) 3 0) DegreeOneSmallSpectrum1226.graph sourceMap0606swap=true := by decide +kernel
theorem fusedMap0606swap_checked : acceptsGraphIso
    (fused (graph core0606) (root 7) 3 0) DegreeOneSmallSpectrum881.graph fusedMap0606swap=true := by decide +kernel
theorem certified0606swap : Certified (graph core0606) (root 7) 3 0 :=
  of_native_maps core0606 DegreeOneSmallSpectrum1226.graph DegreeOneSmallSpectrum881.graph
    sourceMap0606swap fusedMap0606swap sourceMap0606swap_checked fusedMap0606swap_checked
    DegreeOneSmallComparisons.comparison0606
#print axioms sourceMap0606swap_checked
#print axioms fusedMap0606swap_checked
#print axioms certified0606swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
