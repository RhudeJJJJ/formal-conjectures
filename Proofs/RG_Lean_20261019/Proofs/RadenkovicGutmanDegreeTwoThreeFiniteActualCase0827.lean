/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0827 : Family 10 := level10.get ⟨1278,by decide⟩
def sourceMap0827 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (sourceLabel 10 0 0 v)
def fusedMap0827 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0827_checked : acceptsGraphIso
    (source (graph core0827) (root 10) 0 0) DegreeOneSmallSpectrum1920.graph sourceMap0827=true := by decide +kernel
theorem fusedMap0827_checked : acceptsGraphIso
    (fused (graph core0827) (root 10) 0 0) DegreeOneSmallSpectrum1915.graph fusedMap0827=true := by decide +kernel
theorem certified0827 : Certified (graph core0827) (root 10) 0 0 :=
  of_native_maps core0827 DegreeOneSmallSpectrum1920.graph DegreeOneSmallSpectrum1915.graph
    sourceMap0827 fusedMap0827 sourceMap0827_checked fusedMap0827_checked
    DegreeTwoThreeFiniteComparisons.comparison0827
#print axioms sourceMap0827_checked
#print axioms fusedMap0827_checked
#print axioms certified0827
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
