/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0499 : Family 7 := level7.get ⟨9,by decide⟩
def sourceMap0499 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11] (sourceLabel 7 1 1 v)
def fusedMap0499 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0499_checked : acceptsGraphIso
    (source (graph core0499) (root 7) 1 1) DegreeOneSmallSpectrum472.graph sourceMap0499=true := by decide +kernel
theorem fusedMap0499_checked : acceptsGraphIso
    (fused (graph core0499) (root 7) 1 1) DegreeOneSmallSpectrum372.graph fusedMap0499=true := by decide +kernel
theorem certified0499 : Certified (graph core0499) (root 7) 1 1 :=
  of_native_maps core0499 DegreeOneSmallSpectrum472.graph DegreeOneSmallSpectrum372.graph
    sourceMap0499 fusedMap0499 sourceMap0499_checked fusedMap0499_checked
    DegreeOneSmallComparisons.comparison0499
#print axioms sourceMap0499_checked
#print axioms fusedMap0499_checked
#print axioms certified0499
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
