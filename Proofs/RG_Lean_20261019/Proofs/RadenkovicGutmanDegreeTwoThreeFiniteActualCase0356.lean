/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0356 : Family 9 := level9.get ⟨571,by decide⟩
def sourceMap0356 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0356 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0356_checked : acceptsGraphIso
    (source (graph core0356) (root 9) 0 0) DegreeTwoThreeSpectrum559.graph sourceMap0356=true := by decide +kernel
theorem fusedMap0356_checked : acceptsGraphIso
    (fused (graph core0356) (root 9) 0 0) DegreeOneSmallSpectrum647.graph fusedMap0356=true := by decide +kernel
theorem certified0356 : Certified (graph core0356) (root 9) 0 0 :=
  of_native_maps core0356 DegreeTwoThreeSpectrum559.graph DegreeOneSmallSpectrum647.graph
    sourceMap0356 fusedMap0356 sourceMap0356_checked fusedMap0356_checked
    DegreeTwoThreeFiniteComparisons.comparison0356
#print axioms sourceMap0356_checked
#print axioms fusedMap0356_checked
#print axioms certified0356
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
