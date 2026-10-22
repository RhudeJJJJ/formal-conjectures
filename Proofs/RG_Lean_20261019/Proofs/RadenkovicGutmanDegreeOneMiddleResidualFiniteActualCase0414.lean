/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0414 : Family 9 := level9.get ⟨369,by decide⟩
def sourceMap0414 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0414 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0414_checked : acceptsGraphIso
    (source (graph core0414) (root 9) 2 2) DegreeOneMiddleResidualSpectrum783.graph sourceMap0414=true := by decide +kernel
theorem fusedMap0414_checked : acceptsGraphIso
    (fused (graph core0414) (root 9) 2 2) DegreeTwoThreeSpectrum4295.graph fusedMap0414=true := by decide +kernel
theorem certified0414 : Certified (graph core0414) (root 9) 2 2 :=
  of_native_maps core0414 DegreeOneMiddleResidualSpectrum783.graph DegreeTwoThreeSpectrum4295.graph
    sourceMap0414 fusedMap0414 sourceMap0414_checked fusedMap0414_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0414
#print axioms sourceMap0414_checked
#print axioms fusedMap0414_checked
#print axioms certified0414
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
