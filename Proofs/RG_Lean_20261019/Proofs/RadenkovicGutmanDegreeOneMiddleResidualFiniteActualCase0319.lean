/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0319 : Family 9 := level9.get ⟨175,by decide⟩
def sourceMap0319 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0319 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0319_checked : acceptsGraphIso
    (source (graph core0319) (root 9) 2 2) DegreeOneMiddleResidualSpectrum802.graph sourceMap0319=true := by decide +kernel
theorem fusedMap0319_checked : acceptsGraphIso
    (fused (graph core0319) (root 9) 2 2) DegreeTwoThreeSpectrum3942.graph fusedMap0319=true := by decide +kernel
theorem certified0319 : Certified (graph core0319) (root 9) 2 2 :=
  of_native_maps core0319 DegreeOneMiddleResidualSpectrum802.graph DegreeTwoThreeSpectrum3942.graph
    sourceMap0319 fusedMap0319 sourceMap0319_checked fusedMap0319_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0319
#print axioms sourceMap0319_checked
#print axioms fusedMap0319_checked
#print axioms certified0319
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
