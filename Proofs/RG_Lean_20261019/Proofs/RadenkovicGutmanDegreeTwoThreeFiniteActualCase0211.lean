/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0211 : Family 9 := level9.get ⟨195,by decide⟩
def sourceMap0211 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0211 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0211_checked : acceptsGraphIso
    (source (graph core0211) (root 9) 0 0) DegreeOneSmallSpectrum496.graph sourceMap0211=true := by decide +kernel
theorem fusedMap0211_checked : acceptsGraphIso
    (fused (graph core0211) (root 9) 0 0) DegreeOneSmallSpectrum494.graph fusedMap0211=true := by decide +kernel
theorem certified0211 : Certified (graph core0211) (root 9) 0 0 :=
  of_native_maps core0211 DegreeOneSmallSpectrum496.graph DegreeOneSmallSpectrum494.graph
    sourceMap0211 fusedMap0211 sourceMap0211_checked fusedMap0211_checked
    DegreeTwoThreeFiniteComparisons.comparison0211
#print axioms sourceMap0211_checked
#print axioms fusedMap0211_checked
#print axioms certified0211
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
