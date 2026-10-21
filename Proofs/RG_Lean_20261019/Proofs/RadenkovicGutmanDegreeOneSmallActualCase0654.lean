/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0654 : Family 7 := level7.get ⟨51,by decide⟩
def sourceMap0654 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0654 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0654_checked : acceptsGraphIso
    (source (graph core0654) (root 7) 0 3) DegreeOneSmallSpectrum1475.graph sourceMap0654=true := by decide +kernel
theorem fusedMap0654_checked : acceptsGraphIso
    (fused (graph core0654) (root 7) 0 3) DegreeOneSmallSpectrum946.graph fusedMap0654=true := by decide +kernel
theorem certified0654 : Certified (graph core0654) (root 7) 0 3 :=
  of_native_maps core0654 DegreeOneSmallSpectrum1475.graph DegreeOneSmallSpectrum946.graph
    sourceMap0654 fusedMap0654 sourceMap0654_checked fusedMap0654_checked
    DegreeOneSmallComparisons.comparison0654
#print axioms sourceMap0654_checked
#print axioms fusedMap0654_checked
#print axioms certified0654
def sourceMap0654swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0654swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0654swap_checked : acceptsGraphIso
    (source (graph core0654) (root 7) 3 0) DegreeOneSmallSpectrum1475.graph sourceMap0654swap=true := by decide +kernel
theorem fusedMap0654swap_checked : acceptsGraphIso
    (fused (graph core0654) (root 7) 3 0) DegreeOneSmallSpectrum946.graph fusedMap0654swap=true := by decide +kernel
theorem certified0654swap : Certified (graph core0654) (root 7) 3 0 :=
  of_native_maps core0654 DegreeOneSmallSpectrum1475.graph DegreeOneSmallSpectrum946.graph
    sourceMap0654swap fusedMap0654swap sourceMap0654swap_checked fusedMap0654swap_checked
    DegreeOneSmallComparisons.comparison0654
#print axioms sourceMap0654swap_checked
#print axioms fusedMap0654swap_checked
#print axioms certified0654swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
