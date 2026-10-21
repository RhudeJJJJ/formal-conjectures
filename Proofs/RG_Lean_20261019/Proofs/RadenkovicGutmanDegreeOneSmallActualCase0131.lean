/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0131 : Family 4 := level4.get ⟨2,by decide⟩
def sourceMap0131 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (sourceLabel 4 0 4 v)
def fusedMap0131 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10] (fusedLabel 4 0 4 v)
theorem sourceMap0131_checked : acceptsGraphIso
    (source (graph core0131) (root 4) 0 4) DegreeOneSmallSpectrum212.graph sourceMap0131=true := by decide +kernel
theorem fusedMap0131_checked : acceptsGraphIso
    (fused (graph core0131) (root 4) 0 4) DegreeOneSmallSpectrum165.graph fusedMap0131=true := by decide +kernel
theorem certified0131 : Certified (graph core0131) (root 4) 0 4 :=
  of_native_maps core0131 DegreeOneSmallSpectrum212.graph DegreeOneSmallSpectrum165.graph
    sourceMap0131 fusedMap0131 sourceMap0131_checked fusedMap0131_checked
    DegreeOneSmallComparisons.comparison0131
#print axioms sourceMap0131_checked
#print axioms fusedMap0131_checked
#print axioms certified0131
def sourceMap0131swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,7,8,9,10,6] (sourceLabel 4 4 0 v)
def fusedMap0131swap : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10] (fusedLabel 4 4 0 v)
theorem sourceMap0131swap_checked : acceptsGraphIso
    (source (graph core0131) (root 4) 4 0) DegreeOneSmallSpectrum212.graph sourceMap0131swap=true := by decide +kernel
theorem fusedMap0131swap_checked : acceptsGraphIso
    (fused (graph core0131) (root 4) 4 0) DegreeOneSmallSpectrum165.graph fusedMap0131swap=true := by decide +kernel
theorem certified0131swap : Certified (graph core0131) (root 4) 4 0 :=
  of_native_maps core0131 DegreeOneSmallSpectrum212.graph DegreeOneSmallSpectrum165.graph
    sourceMap0131swap fusedMap0131swap sourceMap0131swap_checked fusedMap0131swap_checked
    DegreeOneSmallComparisons.comparison0131
#print axioms sourceMap0131swap_checked
#print axioms fusedMap0131swap_checked
#print axioms certified0131swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
