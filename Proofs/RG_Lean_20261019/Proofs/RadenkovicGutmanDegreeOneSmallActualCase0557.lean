/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0557 : Family 7 := level7.get ⟨22,by decide⟩
def sourceMap0557 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,5,2,3,4] (sourceLabel 7 0 2 v)
def fusedMap0557 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0557_checked : acceptsGraphIso
    (source (graph core0557) (root 7) 0 2) DegreeOneSmallSpectrum584.graph sourceMap0557=true := by decide +kernel
theorem fusedMap0557_checked : acceptsGraphIso
    (fused (graph core0557) (root 7) 0 2) DegreeOneSmallSpectrum394.graph fusedMap0557=true := by decide +kernel
theorem certified0557 : Certified (graph core0557) (root 7) 0 2 :=
  of_native_maps core0557 DegreeOneSmallSpectrum584.graph DegreeOneSmallSpectrum394.graph
    sourceMap0557 fusedMap0557 sourceMap0557_checked fusedMap0557_checked
    DegreeOneSmallComparisons.comparison0557
#print axioms sourceMap0557_checked
#print axioms fusedMap0557_checked
#print axioms certified0557
def sourceMap0557swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 7 2 0 v)
def fusedMap0557swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0557swap_checked : acceptsGraphIso
    (source (graph core0557) (root 7) 2 0) DegreeOneSmallSpectrum584.graph sourceMap0557swap=true := by decide +kernel
theorem fusedMap0557swap_checked : acceptsGraphIso
    (fused (graph core0557) (root 7) 2 0) DegreeOneSmallSpectrum394.graph fusedMap0557swap=true := by decide +kernel
theorem certified0557swap : Certified (graph core0557) (root 7) 2 0 :=
  of_native_maps core0557 DegreeOneSmallSpectrum584.graph DegreeOneSmallSpectrum394.graph
    sourceMap0557swap fusedMap0557swap sourceMap0557swap_checked fusedMap0557swap_checked
    DegreeOneSmallComparisons.comparison0557
#print axioms sourceMap0557swap_checked
#print axioms fusedMap0557swap_checked
#print axioms certified0557swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
