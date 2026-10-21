/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0688 : Family 7 := level7.get ⟨66,by decide⟩
def sourceMap0688 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0688 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0688_checked : acceptsGraphIso
    (source (graph core0688) (root 7) 0 1) DegreeOneSmallSpectrum252.graph sourceMap0688=true := by decide +kernel
theorem fusedMap0688_checked : acceptsGraphIso
    (fused (graph core0688) (root 7) 0 1) DegreeOneSmallSpectrum253.graph fusedMap0688=true := by decide +kernel
theorem certified0688 : Certified (graph core0688) (root 7) 0 1 :=
  of_native_maps core0688 DegreeOneSmallSpectrum252.graph DegreeOneSmallSpectrum253.graph
    sourceMap0688 fusedMap0688 sourceMap0688_checked fusedMap0688_checked
    DegreeOneSmallComparisons.comparison0688
#print axioms sourceMap0688_checked
#print axioms fusedMap0688_checked
#print axioms certified0688
def sourceMap0688swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0688swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0688swap_checked : acceptsGraphIso
    (source (graph core0688) (root 7) 1 0) DegreeOneSmallSpectrum252.graph sourceMap0688swap=true := by decide +kernel
theorem fusedMap0688swap_checked : acceptsGraphIso
    (fused (graph core0688) (root 7) 1 0) DegreeOneSmallSpectrum253.graph fusedMap0688swap=true := by decide +kernel
theorem certified0688swap : Certified (graph core0688) (root 7) 1 0 :=
  of_native_maps core0688 DegreeOneSmallSpectrum252.graph DegreeOneSmallSpectrum253.graph
    sourceMap0688swap fusedMap0688swap sourceMap0688swap_checked fusedMap0688swap_checked
    DegreeOneSmallComparisons.comparison0688
#print axioms sourceMap0688swap_checked
#print axioms fusedMap0688swap_checked
#print axioms certified0688swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
