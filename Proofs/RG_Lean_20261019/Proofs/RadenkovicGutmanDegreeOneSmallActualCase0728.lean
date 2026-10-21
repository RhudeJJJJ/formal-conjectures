/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0728 : Family 7 := level7.get ⟨86,by decide⟩
def sourceMap0728 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0728 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0728_checked : acceptsGraphIso
    (source (graph core0728) (root 7) 1 2) DegreeOneSmallSpectrum1938.graph sourceMap0728=true := by decide +kernel
theorem fusedMap0728_checked : acceptsGraphIso
    (fused (graph core0728) (root 7) 1 2) DegreeOneSmallSpectrum1353.graph fusedMap0728=true := by decide +kernel
theorem certified0728 : Certified (graph core0728) (root 7) 1 2 :=
  of_native_maps core0728 DegreeOneSmallSpectrum1938.graph DegreeOneSmallSpectrum1353.graph
    sourceMap0728 fusedMap0728 sourceMap0728_checked fusedMap0728_checked
    DegreeOneSmallComparisons.comparison0728
#print axioms sourceMap0728_checked
#print axioms fusedMap0728_checked
#print axioms certified0728
def sourceMap0728swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0728swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0728swap_checked : acceptsGraphIso
    (source (graph core0728) (root 7) 2 1) DegreeOneSmallSpectrum1938.graph sourceMap0728swap=true := by decide +kernel
theorem fusedMap0728swap_checked : acceptsGraphIso
    (fused (graph core0728) (root 7) 2 1) DegreeOneSmallSpectrum1353.graph fusedMap0728swap=true := by decide +kernel
theorem certified0728swap : Certified (graph core0728) (root 7) 2 1 :=
  of_native_maps core0728 DegreeOneSmallSpectrum1938.graph DegreeOneSmallSpectrum1353.graph
    sourceMap0728swap fusedMap0728swap sourceMap0728swap_checked fusedMap0728swap_checked
    DegreeOneSmallComparisons.comparison0728
#print axioms sourceMap0728swap_checked
#print axioms fusedMap0728swap_checked
#print axioms certified0728swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
