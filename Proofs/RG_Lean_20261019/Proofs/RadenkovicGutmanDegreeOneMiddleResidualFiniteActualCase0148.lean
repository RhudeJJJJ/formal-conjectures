/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0148 : Family 8 := level8.get ⟨145,by decide⟩
def sourceMap0148 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0148 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0148_checked : acceptsGraphIso
    (source (graph core0148) (root 8) 2 2) DegreeOneMiddleResidualSpectrum312.graph sourceMap0148=true := by decide +kernel
theorem fusedMap0148_checked : acceptsGraphIso
    (fused (graph core0148) (root 8) 2 2) DegreeTwoThreeSpectrum2708.graph fusedMap0148=true := by decide +kernel
theorem certified0148 : Certified (graph core0148) (root 8) 2 2 :=
  of_native_maps core0148 DegreeOneMiddleResidualSpectrum312.graph DegreeTwoThreeSpectrum2708.graph
    sourceMap0148 fusedMap0148 sourceMap0148_checked fusedMap0148_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0148
#print axioms sourceMap0148_checked
#print axioms fusedMap0148_checked
#print axioms certified0148
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
