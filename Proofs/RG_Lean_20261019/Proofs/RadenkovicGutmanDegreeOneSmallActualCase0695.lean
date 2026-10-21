/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0695 : Family 7 := level7.get ⟨70,by decide⟩
def sourceMap0695 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0695 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0695_checked : acceptsGraphIso
    (source (graph core0695) (root 7) 0 2) DegreeOneSmallSpectrum683.graph sourceMap0695=true := by decide +kernel
theorem fusedMap0695_checked : acceptsGraphIso
    (fused (graph core0695) (root 7) 0 2) DegreeOneSmallSpectrum428.graph fusedMap0695=true := by decide +kernel
theorem certified0695 : Certified (graph core0695) (root 7) 0 2 :=
  of_native_maps core0695 DegreeOneSmallSpectrum683.graph DegreeOneSmallSpectrum428.graph
    sourceMap0695 fusedMap0695 sourceMap0695_checked fusedMap0695_checked
    DegreeOneSmallComparisons.comparison0695
#print axioms sourceMap0695_checked
#print axioms fusedMap0695_checked
#print axioms certified0695
def sourceMap0695swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0695swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0695swap_checked : acceptsGraphIso
    (source (graph core0695) (root 7) 2 0) DegreeOneSmallSpectrum683.graph sourceMap0695swap=true := by decide +kernel
theorem fusedMap0695swap_checked : acceptsGraphIso
    (fused (graph core0695) (root 7) 2 0) DegreeOneSmallSpectrum428.graph fusedMap0695swap=true := by decide +kernel
theorem certified0695swap : Certified (graph core0695) (root 7) 2 0 :=
  of_native_maps core0695 DegreeOneSmallSpectrum683.graph DegreeOneSmallSpectrum428.graph
    sourceMap0695swap fusedMap0695swap sourceMap0695swap_checked fusedMap0695swap_checked
    DegreeOneSmallComparisons.comparison0695
#print axioms sourceMap0695swap_checked
#print axioms fusedMap0695swap_checked
#print axioms certified0695swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
