/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0243 : Family 9 := level9.get ⟨56,by decide⟩
def sourceMap0243 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0243 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0243_checked : acceptsGraphIso
    (source (graph core0243) (root 9) 2 2) DegreeOneMiddleResidualSpectrum624.graph sourceMap0243=true := by decide +kernel
theorem fusedMap0243_checked : acceptsGraphIso
    (fused (graph core0243) (root 9) 2 2) DegreeTwoThreeSpectrum3949.graph fusedMap0243=true := by decide +kernel
theorem certified0243 : Certified (graph core0243) (root 9) 2 2 :=
  of_native_maps core0243 DegreeOneMiddleResidualSpectrum624.graph DegreeTwoThreeSpectrum3949.graph
    sourceMap0243 fusedMap0243 sourceMap0243_checked fusedMap0243_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0243
#print axioms sourceMap0243_checked
#print axioms fusedMap0243_checked
#print axioms certified0243
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
