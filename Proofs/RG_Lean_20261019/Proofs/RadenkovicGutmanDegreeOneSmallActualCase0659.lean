/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0659 : Family 7 := level7.get ⟨52,by decide⟩
def sourceMap0659 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0659 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0659_checked : acceptsGraphIso
    (source (graph core0659) (root 7) 0 2) DegreeOneSmallSpectrum570.graph sourceMap0659=true := by decide +kernel
theorem fusedMap0659_checked : acceptsGraphIso
    (fused (graph core0659) (root 7) 0 2) DegreeOneSmallSpectrum571.graph fusedMap0659=true := by decide +kernel
theorem certified0659 : Certified (graph core0659) (root 7) 0 2 :=
  of_native_maps core0659 DegreeOneSmallSpectrum570.graph DegreeOneSmallSpectrum571.graph
    sourceMap0659 fusedMap0659 sourceMap0659_checked fusedMap0659_checked
    DegreeOneSmallComparisons.comparison0659
#print axioms sourceMap0659_checked
#print axioms fusedMap0659_checked
#print axioms certified0659
def sourceMap0659swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0659swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0659swap_checked : acceptsGraphIso
    (source (graph core0659) (root 7) 2 0) DegreeOneSmallSpectrum570.graph sourceMap0659swap=true := by decide +kernel
theorem fusedMap0659swap_checked : acceptsGraphIso
    (fused (graph core0659) (root 7) 2 0) DegreeOneSmallSpectrum571.graph fusedMap0659swap=true := by decide +kernel
theorem certified0659swap : Certified (graph core0659) (root 7) 2 0 :=
  of_native_maps core0659 DegreeOneSmallSpectrum570.graph DegreeOneSmallSpectrum571.graph
    sourceMap0659swap fusedMap0659swap sourceMap0659swap_checked fusedMap0659swap_checked
    DegreeOneSmallComparisons.comparison0659
#print axioms sourceMap0659swap_checked
#print axioms fusedMap0659swap_checked
#print axioms certified0659swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
