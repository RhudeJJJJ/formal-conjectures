/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0264 : Family 9 := level9.get ⟨347,by decide⟩
def sourceMap0264 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0264 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,9,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap0264_checked : acceptsGraphIso
    (source (graph core0264) (root 9) 0 0) DegreeTwoThreeSpectrum555.graph sourceMap0264=true := by decide +kernel
theorem fusedMap0264_checked : acceptsGraphIso
    (fused (graph core0264) (root 9) 0 0) DegreeOneSmallSpectrum668.graph fusedMap0264=true := by decide +kernel
theorem certified0264 : Certified (graph core0264) (root 9) 0 0 :=
  of_native_maps core0264 DegreeTwoThreeSpectrum555.graph DegreeOneSmallSpectrum668.graph
    sourceMap0264 fusedMap0264 sourceMap0264_checked fusedMap0264_checked
    DegreeTwoThreeFiniteComparisons.comparison0264
#print axioms sourceMap0264_checked
#print axioms fusedMap0264_checked
#print axioms certified0264
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
