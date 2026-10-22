/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0883 : Family 10 := level10.get ⟨1410,by decide⟩
def sourceMap0883 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 10 0 0 v)
def fusedMap0883 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0883_checked : acceptsGraphIso
    (source (graph core0883) (root 10) 0 0) DegreeOneSmallSpectrum1979.graph sourceMap0883=true := by decide +kernel
theorem fusedMap0883_checked : acceptsGraphIso
    (fused (graph core0883) (root 10) 0 0) DegreeOneSmallSpectrum1964.graph fusedMap0883=true := by decide +kernel
theorem certified0883 : Certified (graph core0883) (root 10) 0 0 :=
  of_native_maps core0883 DegreeOneSmallSpectrum1979.graph DegreeOneSmallSpectrum1964.graph
    sourceMap0883 fusedMap0883 sourceMap0883_checked fusedMap0883_checked
    DegreeTwoThreeFiniteComparisons.comparison0883
#print axioms sourceMap0883_checked
#print axioms fusedMap0883_checked
#print axioms certified0883
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
