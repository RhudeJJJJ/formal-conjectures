/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0341 : Family 9 := level9.get ⟨215,by decide⟩
def sourceMap0341 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0341 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0341_checked : acceptsGraphIso
    (source (graph core0341) (root 9) 2 2) DegreeOneMiddleResidualSpectrum841.graph sourceMap0341=true := by decide +kernel
theorem fusedMap0341_checked : acceptsGraphIso
    (fused (graph core0341) (root 9) 2 2) DegreeTwoThreeSpectrum4002.graph fusedMap0341=true := by decide +kernel
theorem certified0341 : Certified (graph core0341) (root 9) 2 2 :=
  of_native_maps core0341 DegreeOneMiddleResidualSpectrum841.graph DegreeTwoThreeSpectrum4002.graph
    sourceMap0341 fusedMap0341 sourceMap0341_checked fusedMap0341_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0341
#print axioms sourceMap0341_checked
#print axioms fusedMap0341_checked
#print axioms certified0341
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
