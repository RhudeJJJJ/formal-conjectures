/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0348 : Family 9 := level9.get ⟨227,by decide⟩
def sourceMap0348 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0348 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0348_checked : acceptsGraphIso
    (source (graph core0348) (root 9) 2 2) DegreeOneMiddleResidualSpectrum856.graph sourceMap0348=true := by decide +kernel
theorem fusedMap0348_checked : acceptsGraphIso
    (fused (graph core0348) (root 9) 2 2) DegreeTwoThreeSpectrum4019.graph fusedMap0348=true := by decide +kernel
theorem certified0348 : Certified (graph core0348) (root 9) 2 2 :=
  of_native_maps core0348 DegreeOneMiddleResidualSpectrum856.graph DegreeTwoThreeSpectrum4019.graph
    sourceMap0348 fusedMap0348 sourceMap0348_checked fusedMap0348_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0348
#print axioms sourceMap0348_checked
#print axioms fusedMap0348_checked
#print axioms certified0348
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
