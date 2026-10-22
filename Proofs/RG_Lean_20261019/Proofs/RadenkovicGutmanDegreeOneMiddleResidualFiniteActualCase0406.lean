/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0406 : Family 9 := level9.get ⟨355,by decide⟩
def sourceMap0406 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0406 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0406_checked : acceptsGraphIso
    (source (graph core0406) (root 9) 2 2) DegreeOneMiddleResidualSpectrum770.graph sourceMap0406=true := by decide +kernel
theorem fusedMap0406_checked : acceptsGraphIso
    (fused (graph core0406) (root 9) 2 2) DegreeTwoThreeSpectrum4264.graph fusedMap0406=true := by decide +kernel
theorem certified0406 : Certified (graph core0406) (root 9) 2 2 :=
  of_native_maps core0406 DegreeOneMiddleResidualSpectrum770.graph DegreeTwoThreeSpectrum4264.graph
    sourceMap0406 fusedMap0406 sourceMap0406_checked fusedMap0406_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0406
#print axioms sourceMap0406_checked
#print axioms fusedMap0406_checked
#print axioms certified0406
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
