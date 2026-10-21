/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0612 : Family 7 := level7.get ⟨39,by decide⟩
def sourceMap0612 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0612 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0612_checked : acceptsGraphIso
    (source (graph core0612) (root 7) 0 3) DegreeOneSmallSpectrum1313.graph sourceMap0612=true := by decide +kernel
theorem fusedMap0612_checked : acceptsGraphIso
    (fused (graph core0612) (root 7) 0 3) DegreeOneSmallSpectrum909.graph fusedMap0612=true := by decide +kernel
theorem certified0612 : Certified (graph core0612) (root 7) 0 3 :=
  of_native_maps core0612 DegreeOneSmallSpectrum1313.graph DegreeOneSmallSpectrum909.graph
    sourceMap0612 fusedMap0612 sourceMap0612_checked fusedMap0612_checked
    DegreeOneSmallComparisons.comparison0612
#print axioms sourceMap0612_checked
#print axioms fusedMap0612_checked
#print axioms certified0612
def sourceMap0612swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0612swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0612swap_checked : acceptsGraphIso
    (source (graph core0612) (root 7) 3 0) DegreeOneSmallSpectrum1313.graph sourceMap0612swap=true := by decide +kernel
theorem fusedMap0612swap_checked : acceptsGraphIso
    (fused (graph core0612) (root 7) 3 0) DegreeOneSmallSpectrum909.graph fusedMap0612swap=true := by decide +kernel
theorem certified0612swap : Certified (graph core0612) (root 7) 3 0 :=
  of_native_maps core0612 DegreeOneSmallSpectrum1313.graph DegreeOneSmallSpectrum909.graph
    sourceMap0612swap fusedMap0612swap sourceMap0612swap_checked fusedMap0612swap_checked
    DegreeOneSmallComparisons.comparison0612
#print axioms sourceMap0612swap_checked
#print axioms fusedMap0612swap_checked
#print axioms certified0612swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
