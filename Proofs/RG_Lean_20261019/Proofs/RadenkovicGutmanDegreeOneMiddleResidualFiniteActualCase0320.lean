/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0320 : Family 9 := level9.get ⟨176,by decide⟩
def sourceMap0320 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0320 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0320_checked : acceptsGraphIso
    (source (graph core0320) (root 9) 2 2) DegreeOneMiddleResidualSpectrum805.graph sourceMap0320=true := by decide +kernel
theorem fusedMap0320_checked : acceptsGraphIso
    (fused (graph core0320) (root 9) 2 2) DegreeTwoThreeSpectrum3943.graph fusedMap0320=true := by decide +kernel
theorem certified0320 : Certified (graph core0320) (root 9) 2 2 :=
  of_native_maps core0320 DegreeOneMiddleResidualSpectrum805.graph DegreeTwoThreeSpectrum3943.graph
    sourceMap0320 fusedMap0320 sourceMap0320_checked fusedMap0320_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0320
#print axioms sourceMap0320_checked
#print axioms fusedMap0320_checked
#print axioms certified0320
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
