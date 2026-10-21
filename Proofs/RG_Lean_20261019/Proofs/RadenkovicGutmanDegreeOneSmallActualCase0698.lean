/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0698 : Family 7 := level7.get ⟨70,by decide⟩
def sourceMap0698 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0698 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0698_checked : acceptsGraphIso
    (source (graph core0698) (root 7) 1 2) DegreeOneSmallSpectrum1721.graph sourceMap0698=true := by decide +kernel
theorem fusedMap0698_checked : acceptsGraphIso
    (fused (graph core0698) (root 7) 1 2) DegreeOneSmallSpectrum1088.graph fusedMap0698=true := by decide +kernel
theorem certified0698 : Certified (graph core0698) (root 7) 1 2 :=
  of_native_maps core0698 DegreeOneSmallSpectrum1721.graph DegreeOneSmallSpectrum1088.graph
    sourceMap0698 fusedMap0698 sourceMap0698_checked fusedMap0698_checked
    DegreeOneSmallComparisons.comparison0698
#print axioms sourceMap0698_checked
#print axioms fusedMap0698_checked
#print axioms certified0698
def sourceMap0698swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0698swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0698swap_checked : acceptsGraphIso
    (source (graph core0698) (root 7) 2 1) DegreeOneSmallSpectrum1721.graph sourceMap0698swap=true := by decide +kernel
theorem fusedMap0698swap_checked : acceptsGraphIso
    (fused (graph core0698) (root 7) 2 1) DegreeOneSmallSpectrum1088.graph fusedMap0698swap=true := by decide +kernel
theorem certified0698swap : Certified (graph core0698) (root 7) 2 1 :=
  of_native_maps core0698 DegreeOneSmallSpectrum1721.graph DegreeOneSmallSpectrum1088.graph
    sourceMap0698swap fusedMap0698swap sourceMap0698swap_checked fusedMap0698swap_checked
    DegreeOneSmallComparisons.comparison0698
#print axioms sourceMap0698swap_checked
#print axioms fusedMap0698swap_checked
#print axioms certified0698swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
