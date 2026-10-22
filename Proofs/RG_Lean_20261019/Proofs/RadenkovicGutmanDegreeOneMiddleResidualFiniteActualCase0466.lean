/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0466 : Family 9 := level9.get ⟨550,by decide⟩
def sourceMap0466 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0466 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0466_checked : acceptsGraphIso
    (source (graph core0466) (root 9) 2 2) DegreeOneMiddleResidualSpectrum910.graph sourceMap0466=true := by decide +kernel
theorem fusedMap0466_checked : acceptsGraphIso
    (fused (graph core0466) (root 9) 2 2) DegreeTwoThreeSpectrum4182.graph fusedMap0466=true := by decide +kernel
theorem certified0466 : Certified (graph core0466) (root 9) 2 2 :=
  of_native_maps core0466 DegreeOneMiddleResidualSpectrum910.graph DegreeTwoThreeSpectrum4182.graph
    sourceMap0466 fusedMap0466 sourceMap0466_checked fusedMap0466_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0466
#print axioms sourceMap0466_checked
#print axioms fusedMap0466_checked
#print axioms certified0466
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
