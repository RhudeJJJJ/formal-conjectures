/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0677 : Family 7 := level7.get ⟨63,by decide⟩
def sourceMap0677 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0677 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0677_checked : acceptsGraphIso
    (source (graph core0677) (root 7) 0 2) DegreeOneSmallSpectrum617.graph sourceMap0677=true := by decide +kernel
theorem fusedMap0677_checked : acceptsGraphIso
    (fused (graph core0677) (root 7) 0 2) DegreeOneSmallSpectrum399.graph fusedMap0677=true := by decide +kernel
theorem certified0677 : Certified (graph core0677) (root 7) 0 2 :=
  of_native_maps core0677 DegreeOneSmallSpectrum617.graph DegreeOneSmallSpectrum399.graph
    sourceMap0677 fusedMap0677 sourceMap0677_checked fusedMap0677_checked
    DegreeOneSmallComparisons.comparison0677
#print axioms sourceMap0677_checked
#print axioms fusedMap0677_checked
#print axioms certified0677
def sourceMap0677swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0677swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0677swap_checked : acceptsGraphIso
    (source (graph core0677) (root 7) 2 0) DegreeOneSmallSpectrum617.graph sourceMap0677swap=true := by decide +kernel
theorem fusedMap0677swap_checked : acceptsGraphIso
    (fused (graph core0677) (root 7) 2 0) DegreeOneSmallSpectrum399.graph fusedMap0677swap=true := by decide +kernel
theorem certified0677swap : Certified (graph core0677) (root 7) 2 0 :=
  of_native_maps core0677 DegreeOneSmallSpectrum617.graph DegreeOneSmallSpectrum399.graph
    sourceMap0677swap fusedMap0677swap sourceMap0677swap_checked fusedMap0677swap_checked
    DegreeOneSmallComparisons.comparison0677
#print axioms sourceMap0677swap_checked
#print axioms fusedMap0677swap_checked
#print axioms certified0677swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
