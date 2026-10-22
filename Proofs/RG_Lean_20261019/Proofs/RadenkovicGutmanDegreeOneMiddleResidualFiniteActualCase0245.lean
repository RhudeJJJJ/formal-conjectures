/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0245 : Family 9 := level9.get ⟨58,by decide⟩
def sourceMap0245 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0245 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0245_checked : acceptsGraphIso
    (source (graph core0245) (root 9) 2 2) DegreeOneMiddleResidualSpectrum626.graph sourceMap0245=true := by decide +kernel
theorem fusedMap0245_checked : acceptsGraphIso
    (fused (graph core0245) (root 9) 2 2) DegreeTwoThreeSpectrum3956.graph fusedMap0245=true := by decide +kernel
theorem certified0245 : Certified (graph core0245) (root 9) 2 2 :=
  of_native_maps core0245 DegreeOneMiddleResidualSpectrum626.graph DegreeTwoThreeSpectrum3956.graph
    sourceMap0245 fusedMap0245 sourceMap0245_checked fusedMap0245_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0245
#print axioms sourceMap0245_checked
#print axioms fusedMap0245_checked
#print axioms certified0245
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
