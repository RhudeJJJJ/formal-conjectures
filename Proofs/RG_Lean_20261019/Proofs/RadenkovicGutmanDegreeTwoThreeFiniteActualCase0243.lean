/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0243 : Family 9 := level9.get ⟨291,by decide⟩
def sourceMap0243 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![4,0,8,9,10,11,1,2,3,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap0243 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,5,6,7,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0243_checked : acceptsGraphIso
    (source (graph core0243) (root 9) 0 0) DegreeOneSmallSpectrum564.graph sourceMap0243=true := by decide +kernel
theorem fusedMap0243_checked : acceptsGraphIso
    (fused (graph core0243) (root 9) 0 0) DegreeOneSmallSpectrum535.graph fusedMap0243=true := by decide +kernel
theorem certified0243 : Certified (graph core0243) (root 9) 0 0 :=
  of_native_maps core0243 DegreeOneSmallSpectrum564.graph DegreeOneSmallSpectrum535.graph
    sourceMap0243 fusedMap0243 sourceMap0243_checked fusedMap0243_checked
    DegreeTwoThreeFiniteComparisons.comparison0243
#print axioms sourceMap0243_checked
#print axioms fusedMap0243_checked
#print axioms certified0243
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
