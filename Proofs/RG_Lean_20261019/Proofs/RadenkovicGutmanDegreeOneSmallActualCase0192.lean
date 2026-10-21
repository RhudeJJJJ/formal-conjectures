/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0192 : Family 5 := level5.get ⟨2,by decide⟩
def sourceMap0192 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 5 1 4 v)
def fusedMap0192 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 1 4 v)
theorem sourceMap0192_checked : acceptsGraphIso
    (source (graph core0192) (root 5) 1 4) DegreeOneSmallSpectrum930.graph sourceMap0192=true := by decide +kernel
theorem fusedMap0192_checked : acceptsGraphIso
    (fused (graph core0192) (root 5) 1 4) DegreeOneSmallSpectrum857.graph fusedMap0192=true := by decide +kernel
theorem certified0192 : Certified (graph core0192) (root 5) 1 4 :=
  of_native_maps core0192 DegreeOneSmallSpectrum930.graph DegreeOneSmallSpectrum857.graph
    sourceMap0192 fusedMap0192 sourceMap0192_checked fusedMap0192_checked
    DegreeOneSmallComparisons.comparison0192
#print axioms sourceMap0192_checked
#print axioms fusedMap0192_checked
#print axioms certified0192
def sourceMap0192swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,8,9,10,11,12,6,7] (sourceLabel 5 4 1 v)
def fusedMap0192swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 4 1 v)
theorem sourceMap0192swap_checked : acceptsGraphIso
    (source (graph core0192) (root 5) 4 1) DegreeOneSmallSpectrum930.graph sourceMap0192swap=true := by decide +kernel
theorem fusedMap0192swap_checked : acceptsGraphIso
    (fused (graph core0192) (root 5) 4 1) DegreeOneSmallSpectrum857.graph fusedMap0192swap=true := by decide +kernel
theorem certified0192swap : Certified (graph core0192) (root 5) 4 1 :=
  of_native_maps core0192 DegreeOneSmallSpectrum930.graph DegreeOneSmallSpectrum857.graph
    sourceMap0192swap fusedMap0192swap sourceMap0192swap_checked fusedMap0192swap_checked
    DegreeOneSmallComparisons.comparison0192
#print axioms sourceMap0192swap_checked
#print axioms fusedMap0192swap_checked
#print axioms certified0192swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
