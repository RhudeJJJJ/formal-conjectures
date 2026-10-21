/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0680 : Family 7 := level7.get ⟨63,by decide⟩
def sourceMap0680 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0680 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0680_checked : acceptsGraphIso
    (source (graph core0680) (root 7) 1 2) DegreeOneSmallSpectrum1584.graph sourceMap0680=true := by decide +kernel
theorem fusedMap0680_checked : acceptsGraphIso
    (fused (graph core0680) (root 7) 1 2) DegreeOneSmallSpectrum992.graph fusedMap0680=true := by decide +kernel
theorem certified0680 : Certified (graph core0680) (root 7) 1 2 :=
  of_native_maps core0680 DegreeOneSmallSpectrum1584.graph DegreeOneSmallSpectrum992.graph
    sourceMap0680 fusedMap0680 sourceMap0680_checked fusedMap0680_checked
    DegreeOneSmallComparisons.comparison0680
#print axioms sourceMap0680_checked
#print axioms fusedMap0680_checked
#print axioms certified0680
def sourceMap0680swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0680swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0680swap_checked : acceptsGraphIso
    (source (graph core0680) (root 7) 2 1) DegreeOneSmallSpectrum1584.graph sourceMap0680swap=true := by decide +kernel
theorem fusedMap0680swap_checked : acceptsGraphIso
    (fused (graph core0680) (root 7) 2 1) DegreeOneSmallSpectrum992.graph fusedMap0680swap=true := by decide +kernel
theorem certified0680swap : Certified (graph core0680) (root 7) 2 1 :=
  of_native_maps core0680 DegreeOneSmallSpectrum1584.graph DegreeOneSmallSpectrum992.graph
    sourceMap0680swap fusedMap0680swap sourceMap0680swap_checked fusedMap0680swap_checked
    DegreeOneSmallComparisons.comparison0680
#print axioms sourceMap0680swap_checked
#print axioms fusedMap0680swap_checked
#print axioms certified0680swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
