/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0571 : Family 10 := level10.get ⟨611,by decide⟩
def sourceMap0571 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0571 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0571_checked : acceptsGraphIso
    (source (graph core0571) (root 10) 0 0) DegreeOneSmallSpectrum1179.graph sourceMap0571=true := by decide +kernel
theorem fusedMap0571_checked : acceptsGraphIso
    (fused (graph core0571) (root 10) 0 0) DegreeOneSmallSpectrum1177.graph fusedMap0571=true := by decide +kernel
theorem certified0571 : Certified (graph core0571) (root 10) 0 0 :=
  of_native_maps core0571 DegreeOneSmallSpectrum1179.graph DegreeOneSmallSpectrum1177.graph
    sourceMap0571 fusedMap0571 sourceMap0571_checked fusedMap0571_checked
    DegreeTwoThreeFiniteComparisons.comparison0571
#print axioms sourceMap0571_checked
#print axioms fusedMap0571_checked
#print axioms certified0571
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
