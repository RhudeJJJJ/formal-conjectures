/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0195 : Family 9 := level9.get ⟨146,by decide⟩
def sourceMap0195 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0195 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0195_checked : acceptsGraphIso
    (source (graph core0195) (root 9) 0 0) DegreeTwoThreeSpectrum563.graph sourceMap0195=true := by decide +kernel
theorem fusedMap0195_checked : acceptsGraphIso
    (fused (graph core0195) (root 9) 0 0) DegreeOneSmallSpectrum409.graph fusedMap0195=true := by decide +kernel
theorem certified0195 : Certified (graph core0195) (root 9) 0 0 :=
  of_native_maps core0195 DegreeTwoThreeSpectrum563.graph DegreeOneSmallSpectrum409.graph
    sourceMap0195 fusedMap0195 sourceMap0195_checked fusedMap0195_checked
    DegreeTwoThreeFiniteComparisons.comparison0195
#print axioms sourceMap0195_checked
#print axioms fusedMap0195_checked
#print axioms certified0195
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
