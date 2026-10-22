/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0909 : Family 10 := level10.get ⟨1466,by decide⟩
def sourceMap0909 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0909 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0909_checked : acceptsGraphIso
    (source (graph core0909) (root 10) 0 0) DegreeOneSmallSpectrum1501.graph sourceMap0909=true := by decide +kernel
theorem fusedMap0909_checked : acceptsGraphIso
    (fused (graph core0909) (root 10) 0 0) DegreeOneSmallSpectrum1500.graph fusedMap0909=true := by decide +kernel
theorem certified0909 : Certified (graph core0909) (root 10) 0 0 :=
  of_native_maps core0909 DegreeOneSmallSpectrum1501.graph DegreeOneSmallSpectrum1500.graph
    sourceMap0909 fusedMap0909 sourceMap0909_checked fusedMap0909_checked
    DegreeTwoThreeFiniteComparisons.comparison0909
#print axioms sourceMap0909_checked
#print axioms fusedMap0909_checked
#print axioms certified0909
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
