/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0462 : Family 7 := level7.get ⟨2,by decide⟩
def sourceMap0462 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0462 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0462_checked : acceptsGraphIso
    (source (graph core0462) (root 7) 0 3) DegreeOneSmallSpectrum943.graph sourceMap0462=true := by decide +kernel
theorem fusedMap0462_checked : acceptsGraphIso
    (fused (graph core0462) (root 7) 0 3) DegreeOneSmallSpectrum857.graph fusedMap0462=true := by decide +kernel
theorem certified0462 : Certified (graph core0462) (root 7) 0 3 :=
  of_native_maps core0462 DegreeOneSmallSpectrum943.graph DegreeOneSmallSpectrum857.graph
    sourceMap0462 fusedMap0462 sourceMap0462_checked fusedMap0462_checked
    DegreeOneSmallComparisons.comparison0462
#print axioms sourceMap0462_checked
#print axioms fusedMap0462_checked
#print axioms certified0462
def sourceMap0462swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0462swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0462swap_checked : acceptsGraphIso
    (source (graph core0462) (root 7) 3 0) DegreeOneSmallSpectrum943.graph sourceMap0462swap=true := by decide +kernel
theorem fusedMap0462swap_checked : acceptsGraphIso
    (fused (graph core0462) (root 7) 3 0) DegreeOneSmallSpectrum857.graph fusedMap0462swap=true := by decide +kernel
theorem certified0462swap : Certified (graph core0462) (root 7) 3 0 :=
  of_native_maps core0462 DegreeOneSmallSpectrum943.graph DegreeOneSmallSpectrum857.graph
    sourceMap0462swap fusedMap0462swap sourceMap0462swap_checked fusedMap0462swap_checked
    DegreeOneSmallComparisons.comparison0462
#print axioms sourceMap0462swap_checked
#print axioms fusedMap0462swap_checked
#print axioms certified0462swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
