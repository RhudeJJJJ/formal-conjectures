/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0882 : Family 10 := level10.get ⟨1408,by decide⟩
def sourceMap0882 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 10 0 0 v)
def fusedMap0882 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0882_checked : acceptsGraphIso
    (source (graph core0882) (root 10) 0 0) DegreeOneSmallSpectrum1978.graph sourceMap0882=true := by decide +kernel
theorem fusedMap0882_checked : acceptsGraphIso
    (fused (graph core0882) (root 10) 0 0) DegreeOneSmallSpectrum1963.graph fusedMap0882=true := by decide +kernel
theorem certified0882 : Certified (graph core0882) (root 10) 0 0 :=
  of_native_maps core0882 DegreeOneSmallSpectrum1978.graph DegreeOneSmallSpectrum1963.graph
    sourceMap0882 fusedMap0882 sourceMap0882_checked fusedMap0882_checked
    DegreeTwoThreeFiniteComparisons.comparison0882
#print axioms sourceMap0882_checked
#print axioms fusedMap0882_checked
#print axioms certified0882
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
