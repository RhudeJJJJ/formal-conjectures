/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0291 : Family 9 := level9.get ⟨410,by decide⟩
def sourceMap0291 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap0291 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,4,5,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap0291_checked : acceptsGraphIso
    (source (graph core0291) (root 9) 0 0) DegreeOneSmallSpectrum646.graph sourceMap0291=true := by decide +kernel
theorem fusedMap0291_checked : acceptsGraphIso
    (fused (graph core0291) (root 9) 0 0) DegreeOneSmallSpectrum637.graph fusedMap0291=true := by decide +kernel
theorem certified0291 : Certified (graph core0291) (root 9) 0 0 :=
  of_native_maps core0291 DegreeOneSmallSpectrum646.graph DegreeOneSmallSpectrum637.graph
    sourceMap0291 fusedMap0291 sourceMap0291_checked fusedMap0291_checked
    DegreeTwoThreeFiniteComparisons.comparison0291
#print axioms sourceMap0291_checked
#print axioms fusedMap0291_checked
#print axioms certified0291
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
