/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0106 : Family 4 := level4.get ⟨0,by decide⟩
def sourceMap0106 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (sourceLabel 4 1 5 v)
def fusedMap0106 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 1 5 v)
theorem sourceMap0106_checked : acceptsGraphIso
    (source (graph core0106) (root 4) 1 5) DegreeOneSmallSpectrum971.graph sourceMap0106=true := by decide +kernel
theorem fusedMap0106_checked : acceptsGraphIso
    (fused (graph core0106) (root 4) 1 5) DegreeOneSmallSpectrum861.graph fusedMap0106=true := by decide +kernel
theorem certified0106 : Certified (graph core0106) (root 4) 1 5 :=
  of_native_maps core0106 DegreeOneSmallSpectrum971.graph DegreeOneSmallSpectrum861.graph
    sourceMap0106 fusedMap0106 sourceMap0106_checked fusedMap0106_checked
    DegreeOneSmallComparisons.comparison0106
#print axioms sourceMap0106_checked
#print axioms fusedMap0106_checked
#print axioms certified0106
def sourceMap0106swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,2,3,4,5,0,8,9,10,11,12,6,7] (sourceLabel 4 5 1 v)
def fusedMap0106swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 5 1 v)
theorem sourceMap0106swap_checked : acceptsGraphIso
    (source (graph core0106) (root 4) 5 1) DegreeOneSmallSpectrum971.graph sourceMap0106swap=true := by decide +kernel
theorem fusedMap0106swap_checked : acceptsGraphIso
    (fused (graph core0106) (root 4) 5 1) DegreeOneSmallSpectrum861.graph fusedMap0106swap=true := by decide +kernel
theorem certified0106swap : Certified (graph core0106) (root 4) 5 1 :=
  of_native_maps core0106 DegreeOneSmallSpectrum971.graph DegreeOneSmallSpectrum861.graph
    sourceMap0106swap fusedMap0106swap sourceMap0106swap_checked fusedMap0106swap_checked
    DegreeOneSmallComparisons.comparison0106
#print axioms sourceMap0106swap_checked
#print axioms fusedMap0106swap_checked
#print axioms certified0106swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
