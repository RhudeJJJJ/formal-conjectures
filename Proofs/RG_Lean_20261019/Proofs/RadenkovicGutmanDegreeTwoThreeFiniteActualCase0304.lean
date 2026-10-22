/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0304 : Family 9 := level9.get ⟨449,by decide⟩
def sourceMap0304 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0304 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,9,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap0304_checked : acceptsGraphIso
    (source (graph core0304) (root 9) 0 0) DegreeTwoThreeSpectrum548.graph sourceMap0304=true := by decide +kernel
theorem fusedMap0304_checked : acceptsGraphIso
    (fused (graph core0304) (root 9) 0 0) DegreeOneSmallSpectrum806.graph fusedMap0304=true := by decide +kernel
theorem certified0304 : Certified (graph core0304) (root 9) 0 0 :=
  of_native_maps core0304 DegreeTwoThreeSpectrum548.graph DegreeOneSmallSpectrum806.graph
    sourceMap0304 fusedMap0304 sourceMap0304_checked fusedMap0304_checked
    DegreeTwoThreeFiniteComparisons.comparison0304
#print axioms sourceMap0304_checked
#print axioms fusedMap0304_checked
#print axioms certified0304
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
