/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0338 : Family 9 := level9.get ⟨521,by decide⟩
def sourceMap0338 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap0338 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,4,5,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap0338_checked : acceptsGraphIso
    (source (graph core0338) (root 9) 0 0) DegreeOneSmallSpectrum649.graph sourceMap0338=true := by decide +kernel
theorem fusedMap0338_checked : acceptsGraphIso
    (fused (graph core0338) (root 9) 0 0) DegreeOneSmallSpectrum640.graph fusedMap0338=true := by decide +kernel
theorem certified0338 : Certified (graph core0338) (root 9) 0 0 :=
  of_native_maps core0338 DegreeOneSmallSpectrum649.graph DegreeOneSmallSpectrum640.graph
    sourceMap0338 fusedMap0338 sourceMap0338_checked fusedMap0338_checked
    DegreeTwoThreeFiniteComparisons.comparison0338
#print axioms sourceMap0338_checked
#print axioms fusedMap0338_checked
#print axioms certified0338
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
