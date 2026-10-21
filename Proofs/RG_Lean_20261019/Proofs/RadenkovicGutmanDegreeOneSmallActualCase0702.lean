/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0702 : Family 7 := level7.get ⟨71,by decide⟩
def sourceMap0702 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 0 3 v)
def fusedMap0702 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0702_checked : acceptsGraphIso
    (source (graph core0702) (root 7) 0 3) DegreeOneSmallSpectrum1091.graph sourceMap0702=true := by decide +kernel
theorem fusedMap0702_checked : acceptsGraphIso
    (fused (graph core0702) (root 7) 0 3) DegreeOneSmallSpectrum1095.graph fusedMap0702=true := by decide +kernel
theorem certified0702 : Certified (graph core0702) (root 7) 0 3 :=
  of_native_maps core0702 DegreeOneSmallSpectrum1091.graph DegreeOneSmallSpectrum1095.graph
    sourceMap0702 fusedMap0702 sourceMap0702_checked fusedMap0702_checked
    DegreeOneSmallComparisons.comparison0702
#print axioms sourceMap0702_checked
#print axioms fusedMap0702_checked
#print axioms certified0702
def sourceMap0702swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,8] (sourceLabel 7 3 0 v)
def fusedMap0702swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0702swap_checked : acceptsGraphIso
    (source (graph core0702) (root 7) 3 0) DegreeOneSmallSpectrum1091.graph sourceMap0702swap=true := by decide +kernel
theorem fusedMap0702swap_checked : acceptsGraphIso
    (fused (graph core0702) (root 7) 3 0) DegreeOneSmallSpectrum1095.graph fusedMap0702swap=true := by decide +kernel
theorem certified0702swap : Certified (graph core0702) (root 7) 3 0 :=
  of_native_maps core0702 DegreeOneSmallSpectrum1091.graph DegreeOneSmallSpectrum1095.graph
    sourceMap0702swap fusedMap0702swap sourceMap0702swap_checked fusedMap0702swap_checked
    DegreeOneSmallComparisons.comparison0702
#print axioms sourceMap0702swap_checked
#print axioms fusedMap0702swap_checked
#print axioms certified0702swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
