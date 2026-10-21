/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0684 : Family 7 := level7.get ⟨65,by decide⟩
def sourceMap0684 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 0 3 v)
def fusedMap0684 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0684_checked : acceptsGraphIso
    (source (graph core0684) (root 7) 0 3) DegreeOneSmallSpectrum1011.graph sourceMap0684=true := by decide +kernel
theorem fusedMap0684_checked : acceptsGraphIso
    (fused (graph core0684) (root 7) 0 3) DegreeOneSmallSpectrum1015.graph fusedMap0684=true := by decide +kernel
theorem certified0684 : Certified (graph core0684) (root 7) 0 3 :=
  of_native_maps core0684 DegreeOneSmallSpectrum1011.graph DegreeOneSmallSpectrum1015.graph
    sourceMap0684 fusedMap0684 sourceMap0684_checked fusedMap0684_checked
    DegreeOneSmallComparisons.comparison0684
#print axioms sourceMap0684_checked
#print axioms fusedMap0684_checked
#print axioms certified0684
def sourceMap0684swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,8] (sourceLabel 7 3 0 v)
def fusedMap0684swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0684swap_checked : acceptsGraphIso
    (source (graph core0684) (root 7) 3 0) DegreeOneSmallSpectrum1011.graph sourceMap0684swap=true := by decide +kernel
theorem fusedMap0684swap_checked : acceptsGraphIso
    (fused (graph core0684) (root 7) 3 0) DegreeOneSmallSpectrum1015.graph fusedMap0684swap=true := by decide +kernel
theorem certified0684swap : Certified (graph core0684) (root 7) 3 0 :=
  of_native_maps core0684 DegreeOneSmallSpectrum1011.graph DegreeOneSmallSpectrum1015.graph
    sourceMap0684swap fusedMap0684swap sourceMap0684swap_checked fusedMap0684swap_checked
    DegreeOneSmallComparisons.comparison0684
#print axioms sourceMap0684swap_checked
#print axioms fusedMap0684swap_checked
#print axioms certified0684swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
