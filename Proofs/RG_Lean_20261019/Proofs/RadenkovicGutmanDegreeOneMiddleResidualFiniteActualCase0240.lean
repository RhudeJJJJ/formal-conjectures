/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0240 : Family 9 := level9.get ⟨52,by decide⟩
def sourceMap0240 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0240 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0240_checked : acceptsGraphIso
    (source (graph core0240) (root 9) 2 2) DegreeOneMiddleResidualSpectrum612.graph sourceMap0240=true := by decide +kernel
theorem fusedMap0240_checked : acceptsGraphIso
    (fused (graph core0240) (root 9) 2 2) DegreeTwoThreeSpectrum3935.graph fusedMap0240=true := by decide +kernel
theorem certified0240 : Certified (graph core0240) (root 9) 2 2 :=
  of_native_maps core0240 DegreeOneMiddleResidualSpectrum612.graph DegreeTwoThreeSpectrum3935.graph
    sourceMap0240 fusedMap0240 sourceMap0240_checked fusedMap0240_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0240
#print axioms sourceMap0240_checked
#print axioms fusedMap0240_checked
#print axioms certified0240
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
