/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0291 : Family 9 := level9.get ⟨127,by decide⟩
def sourceMap0291 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,11,12,13,14,15,8,9,10,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0291 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0291_checked : acceptsGraphIso
    (source (graph core0291) (root 9) 2 2) DegreeTwoThreeSpectrum4558.graph sourceMap0291=true := by decide +kernel
theorem fusedMap0291_checked : acceptsGraphIso
    (fused (graph core0291) (root 9) 2 2) DegreeTwoThreeSpectrum4160.graph fusedMap0291=true := by decide +kernel
theorem certified0291 : Certified (graph core0291) (root 9) 2 2 :=
  of_native_maps core0291 DegreeTwoThreeSpectrum4558.graph DegreeTwoThreeSpectrum4160.graph
    sourceMap0291 fusedMap0291 sourceMap0291_checked fusedMap0291_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0291
#print axioms sourceMap0291_checked
#print axioms fusedMap0291_checked
#print axioms certified0291
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
