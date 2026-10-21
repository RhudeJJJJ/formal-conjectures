/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0690 : Family 7 := level7.get ⟨66,by decide⟩
def sourceMap0690 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 0 3 v)
def fusedMap0690 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0690_checked : acceptsGraphIso
    (source (graph core0690) (root 7) 0 3) DegreeOneSmallSpectrum1017.graph sourceMap0690=true := by decide +kernel
theorem fusedMap0690_checked : acceptsGraphIso
    (fused (graph core0690) (root 7) 0 3) DegreeOneSmallSpectrum1021.graph fusedMap0690=true := by decide +kernel
theorem certified0690 : Certified (graph core0690) (root 7) 0 3 :=
  of_native_maps core0690 DegreeOneSmallSpectrum1017.graph DegreeOneSmallSpectrum1021.graph
    sourceMap0690 fusedMap0690 sourceMap0690_checked fusedMap0690_checked
    DegreeOneSmallComparisons.comparison0690
#print axioms sourceMap0690_checked
#print axioms fusedMap0690_checked
#print axioms certified0690
def sourceMap0690swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,8] (sourceLabel 7 3 0 v)
def fusedMap0690swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0690swap_checked : acceptsGraphIso
    (source (graph core0690) (root 7) 3 0) DegreeOneSmallSpectrum1017.graph sourceMap0690swap=true := by decide +kernel
theorem fusedMap0690swap_checked : acceptsGraphIso
    (fused (graph core0690) (root 7) 3 0) DegreeOneSmallSpectrum1021.graph fusedMap0690swap=true := by decide +kernel
theorem certified0690swap : Certified (graph core0690) (root 7) 3 0 :=
  of_native_maps core0690 DegreeOneSmallSpectrum1017.graph DegreeOneSmallSpectrum1021.graph
    sourceMap0690swap fusedMap0690swap sourceMap0690swap_checked fusedMap0690swap_checked
    DegreeOneSmallComparisons.comparison0690
#print axioms sourceMap0690swap_checked
#print axioms fusedMap0690swap_checked
#print axioms certified0690swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
