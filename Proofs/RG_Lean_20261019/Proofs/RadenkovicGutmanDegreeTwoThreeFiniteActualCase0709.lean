/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0709 : Family 10 := level10.get ⟨977,by decide⟩
def sourceMap0709 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0709 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0709_checked : acceptsGraphIso
    (source (graph core0709) (root 10) 0 0) DegreeOneSmallSpectrum931.graph sourceMap0709=true := by decide +kernel
theorem fusedMap0709_checked : acceptsGraphIso
    (fused (graph core0709) (root 10) 0 0) DegreeOneSmallSpectrum930.graph fusedMap0709=true := by decide +kernel
theorem certified0709 : Certified (graph core0709) (root 10) 0 0 :=
  of_native_maps core0709 DegreeOneSmallSpectrum931.graph DegreeOneSmallSpectrum930.graph
    sourceMap0709 fusedMap0709 sourceMap0709_checked fusedMap0709_checked
    DegreeTwoThreeFiniteComparisons.comparison0709
#print axioms sourceMap0709_checked
#print axioms fusedMap0709_checked
#print axioms certified0709
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
