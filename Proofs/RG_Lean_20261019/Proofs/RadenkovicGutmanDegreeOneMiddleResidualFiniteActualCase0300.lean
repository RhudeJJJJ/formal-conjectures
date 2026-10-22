/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0300 : Family 9 := level9.get ⟨145,by decide⟩
def sourceMap0300 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0300 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0300_checked : acceptsGraphIso
    (source (graph core0300) (root 9) 2 2) DegreeOneMiddleResidualSpectrum759.graph sourceMap0300=true := by decide +kernel
theorem fusedMap0300_checked : acceptsGraphIso
    (fused (graph core0300) (root 9) 2 2) DegreeTwoThreeSpectrum3900.graph fusedMap0300=true := by decide +kernel
theorem certified0300 : Certified (graph core0300) (root 9) 2 2 :=
  of_native_maps core0300 DegreeOneMiddleResidualSpectrum759.graph DegreeTwoThreeSpectrum3900.graph
    sourceMap0300 fusedMap0300 sourceMap0300_checked fusedMap0300_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0300
#print axioms sourceMap0300_checked
#print axioms fusedMap0300_checked
#print axioms certified0300
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
