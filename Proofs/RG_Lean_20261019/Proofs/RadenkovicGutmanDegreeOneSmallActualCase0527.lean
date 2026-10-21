/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0527 : Family 7 := level7.get ⟨15,by decide⟩
def sourceMap0527 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,11,10,7,8,9] (sourceLabel 7 0 2 v)
def fusedMap0527 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0527_checked : acceptsGraphIso
    (source (graph core0527) (root 7) 0 2) DegreeOneSmallSpectrum558.graph sourceMap0527=true := by decide +kernel
theorem fusedMap0527_checked : acceptsGraphIso
    (fused (graph core0527) (root 7) 0 2) DegreeOneSmallSpectrum382.graph fusedMap0527=true := by decide +kernel
theorem certified0527 : Certified (graph core0527) (root 7) 0 2 :=
  of_native_maps core0527 DegreeOneSmallSpectrum558.graph DegreeOneSmallSpectrum382.graph
    sourceMap0527 fusedMap0527 sourceMap0527_checked fusedMap0527_checked
    DegreeOneSmallComparisons.comparison0527
#print axioms sourceMap0527_checked
#print axioms fusedMap0527_checked
#print axioms certified0527
def sourceMap0527swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,11,7,8,9,10] (sourceLabel 7 2 0 v)
def fusedMap0527swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0527swap_checked : acceptsGraphIso
    (source (graph core0527) (root 7) 2 0) DegreeOneSmallSpectrum558.graph sourceMap0527swap=true := by decide +kernel
theorem fusedMap0527swap_checked : acceptsGraphIso
    (fused (graph core0527) (root 7) 2 0) DegreeOneSmallSpectrum382.graph fusedMap0527swap=true := by decide +kernel
theorem certified0527swap : Certified (graph core0527) (root 7) 2 0 :=
  of_native_maps core0527 DegreeOneSmallSpectrum558.graph DegreeOneSmallSpectrum382.graph
    sourceMap0527swap fusedMap0527swap sourceMap0527swap_checked fusedMap0527swap_checked
    DegreeOneSmallComparisons.comparison0527
#print axioms sourceMap0527swap_checked
#print axioms fusedMap0527swap_checked
#print axioms certified0527swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
