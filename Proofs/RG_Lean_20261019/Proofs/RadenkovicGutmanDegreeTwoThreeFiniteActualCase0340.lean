/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0340 : Family 9 := level9.get ⟨528,by decide⟩
def sourceMap0340 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap0340 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,3,4,5,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap0340_checked : acceptsGraphIso
    (source (graph core0340) (root 9) 0 0) DegreeOneSmallSpectrum442.graph sourceMap0340=true := by decide +kernel
theorem fusedMap0340_checked : acceptsGraphIso
    (fused (graph core0340) (root 9) 0 0) DegreeOneSmallSpectrum441.graph fusedMap0340=true := by decide +kernel
theorem certified0340 : Certified (graph core0340) (root 9) 0 0 :=
  of_native_maps core0340 DegreeOneSmallSpectrum442.graph DegreeOneSmallSpectrum441.graph
    sourceMap0340 fusedMap0340 sourceMap0340_checked fusedMap0340_checked
    DegreeTwoThreeFiniteComparisons.comparison0340
#print axioms sourceMap0340_checked
#print axioms fusedMap0340_checked
#print axioms certified0340
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
