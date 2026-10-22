/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0162 : Family 8 := level8.get ⟨192,by decide⟩
def sourceMap0162 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0162 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0162_checked : acceptsGraphIso
    (source (graph core0162) (root 8) 2 2) DegreeOneMiddleResidualSpectrum346.graph sourceMap0162=true := by decide +kernel
theorem fusedMap0162_checked : acceptsGraphIso
    (fused (graph core0162) (root 8) 2 2) DegreeTwoThreeSpectrum2441.graph fusedMap0162=true := by decide +kernel
theorem certified0162 : Certified (graph core0162) (root 8) 2 2 :=
  of_native_maps core0162 DegreeOneMiddleResidualSpectrum346.graph DegreeTwoThreeSpectrum2441.graph
    sourceMap0162 fusedMap0162 sourceMap0162_checked fusedMap0162_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0162
#print axioms sourceMap0162_checked
#print axioms fusedMap0162_checked
#print axioms certified0162
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
