/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0140 : Family 8 := level8.get ⟨132,by decide⟩
def sourceMap0140 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0140 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0140_checked : acceptsGraphIso
    (source (graph core0140) (root 8) 2 2) DegreeOneMiddleResidualSpectrum298.graph sourceMap0140=true := by decide +kernel
theorem fusedMap0140_checked : acceptsGraphIso
    (fused (graph core0140) (root 8) 2 2) DegreeTwoThreeSpectrum2648.graph fusedMap0140=true := by decide +kernel
theorem certified0140 : Certified (graph core0140) (root 8) 2 2 :=
  of_native_maps core0140 DegreeOneMiddleResidualSpectrum298.graph DegreeTwoThreeSpectrum2648.graph
    sourceMap0140 fusedMap0140 sourceMap0140_checked fusedMap0140_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0140
#print axioms sourceMap0140_checked
#print axioms fusedMap0140_checked
#print axioms certified0140
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
