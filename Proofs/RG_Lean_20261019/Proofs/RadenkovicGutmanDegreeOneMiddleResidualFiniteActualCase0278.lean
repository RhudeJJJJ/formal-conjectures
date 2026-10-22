/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0278 : Family 9 := level9.get ⟨105,by decide⟩
def sourceMap0278 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0278 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0278_checked : acceptsGraphIso
    (source (graph core0278) (root 9) 2 2) DegreeOneMiddleResidualSpectrum702.graph sourceMap0278=true := by decide +kernel
theorem fusedMap0278_checked : acceptsGraphIso
    (fused (graph core0278) (root 9) 2 2) DegreeTwoThreeSpectrum4101.graph fusedMap0278=true := by decide +kernel
theorem certified0278 : Certified (graph core0278) (root 9) 2 2 :=
  of_native_maps core0278 DegreeOneMiddleResidualSpectrum702.graph DegreeTwoThreeSpectrum4101.graph
    sourceMap0278 fusedMap0278 sourceMap0278_checked fusedMap0278_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0278
#print axioms sourceMap0278_checked
#print axioms fusedMap0278_checked
#print axioms certified0278
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
