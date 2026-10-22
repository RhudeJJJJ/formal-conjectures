/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0318 : Family 9 := level9.get ⟨174,by decide⟩
def sourceMap0318 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0318 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0318_checked : acceptsGraphIso
    (source (graph core0318) (root 9) 2 2) DegreeOneMiddleResidualSpectrum799.graph sourceMap0318=true := by decide +kernel
theorem fusedMap0318_checked : acceptsGraphIso
    (fused (graph core0318) (root 9) 2 2) DegreeTwoThreeSpectrum3941.graph fusedMap0318=true := by decide +kernel
theorem certified0318 : Certified (graph core0318) (root 9) 2 2 :=
  of_native_maps core0318 DegreeOneMiddleResidualSpectrum799.graph DegreeTwoThreeSpectrum3941.graph
    sourceMap0318 fusedMap0318 sourceMap0318_checked fusedMap0318_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0318
#print axioms sourceMap0318_checked
#print axioms fusedMap0318_checked
#print axioms certified0318
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
