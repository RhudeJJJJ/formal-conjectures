/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0907 : Family 10 := level10.get ⟨1462,by decide⟩
def sourceMap0907 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0907 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,6,7,8,9,10,11,12,1,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0907_checked : acceptsGraphIso
    (source (graph core0907) (root 10) 0 0) DegreeOneSmallSpectrum1495.graph sourceMap0907=true := by decide +kernel
theorem fusedMap0907_checked : acceptsGraphIso
    (fused (graph core0907) (root 10) 0 0) DegreeOneSmallSpectrum1487.graph fusedMap0907=true := by decide +kernel
theorem certified0907 : Certified (graph core0907) (root 10) 0 0 :=
  of_native_maps core0907 DegreeOneSmallSpectrum1495.graph DegreeOneSmallSpectrum1487.graph
    sourceMap0907 fusedMap0907 sourceMap0907_checked fusedMap0907_checked
    DegreeTwoThreeFiniteComparisons.comparison0907
#print axioms sourceMap0907_checked
#print axioms fusedMap0907_checked
#print axioms certified0907
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
