/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0322 : Family 9 := level9.get ⟨489,by decide⟩
def sourceMap0322 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0322 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0322_checked : acceptsGraphIso
    (source (graph core0322) (root 9) 0 0) DegreeOneSmallSpectrum808.graph sourceMap0322=true := by decide +kernel
theorem fusedMap0322_checked : acceptsGraphIso
    (fused (graph core0322) (root 9) 0 0) DegreeOneSmallSpectrum794.graph fusedMap0322=true := by decide +kernel
theorem certified0322 : Certified (graph core0322) (root 9) 0 0 :=
  of_native_maps core0322 DegreeOneSmallSpectrum808.graph DegreeOneSmallSpectrum794.graph
    sourceMap0322 fusedMap0322 sourceMap0322_checked fusedMap0322_checked
    DegreeTwoThreeFiniteComparisons.comparison0322
#print axioms sourceMap0322_checked
#print axioms fusedMap0322_checked
#print axioms certified0322
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
