/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0230 : Family 9 := level9.get ⟨253,by decide⟩
def sourceMap0230 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0230 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0230_checked : acceptsGraphIso
    (source (graph core0230) (root 9) 0 0) DegreeOneSmallSpectrum669.graph sourceMap0230=true := by decide +kernel
theorem fusedMap0230_checked : acceptsGraphIso
    (fused (graph core0230) (root 9) 0 0) DegreeOneSmallSpectrum552.graph fusedMap0230=true := by decide +kernel
theorem certified0230 : Certified (graph core0230) (root 9) 0 0 :=
  of_native_maps core0230 DegreeOneSmallSpectrum669.graph DegreeOneSmallSpectrum552.graph
    sourceMap0230 fusedMap0230 sourceMap0230_checked fusedMap0230_checked
    DegreeTwoThreeFiniteComparisons.comparison0230
#print axioms sourceMap0230_checked
#print axioms fusedMap0230_checked
#print axioms certified0230
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
