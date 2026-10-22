/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0348 : Family 9 := level9.get ⟨554,by decide⟩
def sourceMap0348 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 9 0 0 v)
def fusedMap0348 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0348_checked : acceptsGraphIso
    (source (graph core0348) (root 9) 0 0) DegreeTwoThreeSpectrum711.graph sourceMap0348=true := by decide +kernel
theorem fusedMap0348_checked : acceptsGraphIso
    (fused (graph core0348) (root 9) 0 0) DegreeOneSmallSpectrum611.graph fusedMap0348=true := by decide +kernel
theorem certified0348 : Certified (graph core0348) (root 9) 0 0 :=
  of_native_maps core0348 DegreeTwoThreeSpectrum711.graph DegreeOneSmallSpectrum611.graph
    sourceMap0348 fusedMap0348 sourceMap0348_checked fusedMap0348_checked
    DegreeTwoThreeFiniteComparisons.comparison0348
#print axioms sourceMap0348_checked
#print axioms fusedMap0348_checked
#print axioms certified0348
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
