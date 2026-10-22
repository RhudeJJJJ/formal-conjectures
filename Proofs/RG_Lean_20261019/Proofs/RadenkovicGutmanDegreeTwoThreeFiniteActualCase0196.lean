/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0196 : Family 9 := level9.get ⟨150,by decide⟩
def sourceMap0196 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0196 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0196_checked : acceptsGraphIso
    (source (graph core0196) (root 9) 0 0) DegreeTwoThreeSpectrum575.graph sourceMap0196=true := by decide +kernel
theorem fusedMap0196_checked : acceptsGraphIso
    (fused (graph core0196) (root 9) 0 0) DegreeOneSmallSpectrum415.graph fusedMap0196=true := by decide +kernel
theorem certified0196 : Certified (graph core0196) (root 9) 0 0 :=
  of_native_maps core0196 DegreeTwoThreeSpectrum575.graph DegreeOneSmallSpectrum415.graph
    sourceMap0196 fusedMap0196 sourceMap0196_checked fusedMap0196_checked
    DegreeTwoThreeFiniteComparisons.comparison0196
#print axioms sourceMap0196_checked
#print axioms fusedMap0196_checked
#print axioms certified0196
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
