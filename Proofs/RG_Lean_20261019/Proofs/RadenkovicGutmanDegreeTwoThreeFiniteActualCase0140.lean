/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0140 : Family 8 := level8.get ⟨219,by decide⟩
def sourceMap0140 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,6,7,8,9,10,1,2,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0140 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,6,7,8,9,10,1,2,3,4,5] (fusedLabel 8 0 0 v)
theorem sourceMap0140_checked : acceptsGraphIso
    (source (graph core0140) (root 8) 0 0) DegreeOneSmallSpectrum286.graph sourceMap0140=true := by decide +kernel
theorem fusedMap0140_checked : acceptsGraphIso
    (fused (graph core0140) (root 8) 0 0) DegreeOneSmallSpectrum276.graph fusedMap0140=true := by decide +kernel
theorem certified0140 : Certified (graph core0140) (root 8) 0 0 :=
  of_native_maps core0140 DegreeOneSmallSpectrum286.graph DegreeOneSmallSpectrum276.graph
    sourceMap0140 fusedMap0140 sourceMap0140_checked fusedMap0140_checked
    DegreeTwoThreeFiniteComparisons.comparison0140
#print axioms sourceMap0140_checked
#print axioms fusedMap0140_checked
#print axioms certified0140
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
