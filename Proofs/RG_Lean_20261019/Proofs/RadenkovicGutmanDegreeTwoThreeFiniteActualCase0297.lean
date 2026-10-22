/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0297 : Family 9 := level9.get ⟨431,by decide⟩
def sourceMap0297 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0297 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,9,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap0297_checked : acceptsGraphIso
    (source (graph core0297) (root 9) 0 0) DegreeOneSmallSpectrum647.graph sourceMap0297=true := by decide +kernel
theorem fusedMap0297_checked : acceptsGraphIso
    (fused (graph core0297) (root 9) 0 0) DegreeOneSmallSpectrum793.graph fusedMap0297=true := by decide +kernel
theorem certified0297 : Certified (graph core0297) (root 9) 0 0 :=
  of_native_maps core0297 DegreeOneSmallSpectrum647.graph DegreeOneSmallSpectrum793.graph
    sourceMap0297 fusedMap0297 sourceMap0297_checked fusedMap0297_checked
    DegreeTwoThreeFiniteComparisons.comparison0297
#print axioms sourceMap0297_checked
#print axioms fusedMap0297_checked
#print axioms certified0297
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
