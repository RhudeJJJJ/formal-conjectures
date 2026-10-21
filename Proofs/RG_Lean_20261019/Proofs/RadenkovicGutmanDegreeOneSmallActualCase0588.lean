/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0588 : Family 7 := level7.get ⟨31,by decide⟩
def sourceMap0588 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0588 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0588_checked : acceptsGraphIso
    (source (graph core0588) (root 7) 0 3) DegreeOneSmallSpectrum1135.graph sourceMap0588=true := by decide +kernel
theorem fusedMap0588_checked : acceptsGraphIso
    (fused (graph core0588) (root 7) 0 3) DegreeOneSmallSpectrum872.graph fusedMap0588=true := by decide +kernel
theorem certified0588 : Certified (graph core0588) (root 7) 0 3 :=
  of_native_maps core0588 DegreeOneSmallSpectrum1135.graph DegreeOneSmallSpectrum872.graph
    sourceMap0588 fusedMap0588 sourceMap0588_checked fusedMap0588_checked
    DegreeOneSmallComparisons.comparison0588
#print axioms sourceMap0588_checked
#print axioms fusedMap0588_checked
#print axioms certified0588
def sourceMap0588swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0588swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0588swap_checked : acceptsGraphIso
    (source (graph core0588) (root 7) 3 0) DegreeOneSmallSpectrum1135.graph sourceMap0588swap=true := by decide +kernel
theorem fusedMap0588swap_checked : acceptsGraphIso
    (fused (graph core0588) (root 7) 3 0) DegreeOneSmallSpectrum872.graph fusedMap0588swap=true := by decide +kernel
theorem certified0588swap : Certified (graph core0588) (root 7) 3 0 :=
  of_native_maps core0588 DegreeOneSmallSpectrum1135.graph DegreeOneSmallSpectrum872.graph
    sourceMap0588swap fusedMap0588swap sourceMap0588swap_checked fusedMap0588swap_checked
    DegreeOneSmallComparisons.comparison0588
#print axioms sourceMap0588swap_checked
#print axioms fusedMap0588swap_checked
#print axioms certified0588swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
