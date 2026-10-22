/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0875 : Family 10 := level10.get ⟨1387,by decide⟩
def sourceMap0875 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0875 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0875_checked : acceptsGraphIso
    (source (graph core0875) (root 10) 0 0) DegreeOneSmallSpectrum1437.graph sourceMap0875=true := by decide +kernel
theorem fusedMap0875_checked : acceptsGraphIso
    (fused (graph core0875) (root 10) 0 0) DegreeOneSmallSpectrum1436.graph fusedMap0875=true := by decide +kernel
theorem certified0875 : Certified (graph core0875) (root 10) 0 0 :=
  of_native_maps core0875 DegreeOneSmallSpectrum1437.graph DegreeOneSmallSpectrum1436.graph
    sourceMap0875 fusedMap0875 sourceMap0875_checked fusedMap0875_checked
    DegreeTwoThreeFiniteComparisons.comparison0875
#print axioms sourceMap0875_checked
#print axioms fusedMap0875_checked
#print axioms certified0875
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
