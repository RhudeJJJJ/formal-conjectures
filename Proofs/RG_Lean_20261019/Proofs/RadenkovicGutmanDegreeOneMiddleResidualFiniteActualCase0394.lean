/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0394 : Family 9 := level9.get ⟨330,by decide⟩
def sourceMap0394 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0394 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0394_checked : acceptsGraphIso
    (source (graph core0394) (root 9) 2 2) DegreeOneMiddleResidualSpectrum749.graph sourceMap0394=true := by decide +kernel
theorem fusedMap0394_checked : acceptsGraphIso
    (fused (graph core0394) (root 9) 2 2) DegreeTwoThreeSpectrum4207.graph fusedMap0394=true := by decide +kernel
theorem certified0394 : Certified (graph core0394) (root 9) 2 2 :=
  of_native_maps core0394 DegreeOneMiddleResidualSpectrum749.graph DegreeTwoThreeSpectrum4207.graph
    sourceMap0394 fusedMap0394 sourceMap0394_checked fusedMap0394_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0394
#print axioms sourceMap0394_checked
#print axioms fusedMap0394_checked
#print axioms certified0394
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
