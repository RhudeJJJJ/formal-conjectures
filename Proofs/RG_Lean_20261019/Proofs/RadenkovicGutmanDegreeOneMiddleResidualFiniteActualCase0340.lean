/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0340 : Family 9 := level9.get ⟨214,by decide⟩
def sourceMap0340 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0340 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0340_checked : acceptsGraphIso
    (source (graph core0340) (root 9) 2 2) DegreeOneMiddleResidualSpectrum840.graph sourceMap0340=true := by decide +kernel
theorem fusedMap0340_checked : acceptsGraphIso
    (fused (graph core0340) (root 9) 2 2) DegreeTwoThreeSpectrum4001.graph fusedMap0340=true := by decide +kernel
theorem certified0340 : Certified (graph core0340) (root 9) 2 2 :=
  of_native_maps core0340 DegreeOneMiddleResidualSpectrum840.graph DegreeTwoThreeSpectrum4001.graph
    sourceMap0340 fusedMap0340 sourceMap0340_checked fusedMap0340_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0340
#print axioms sourceMap0340_checked
#print axioms fusedMap0340_checked
#print axioms certified0340
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
