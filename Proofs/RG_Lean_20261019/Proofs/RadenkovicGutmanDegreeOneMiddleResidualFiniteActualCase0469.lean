/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0469 : Family 9 := level9.get ⟨561,by decide⟩
def sourceMap0469 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0469 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0469_checked : acceptsGraphIso
    (source (graph core0469) (root 9) 2 2) DegreeOneMiddleResidualSpectrum913.graph sourceMap0469=true := by decide +kernel
theorem fusedMap0469_checked : acceptsGraphIso
    (fused (graph core0469) (root 9) 2 2) DegreeTwoThreeSpectrum4204.graph fusedMap0469=true := by decide +kernel
theorem certified0469 : Certified (graph core0469) (root 9) 2 2 :=
  of_native_maps core0469 DegreeOneMiddleResidualSpectrum913.graph DegreeTwoThreeSpectrum4204.graph
    sourceMap0469 fusedMap0469 sourceMap0469_checked fusedMap0469_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0469
#print axioms sourceMap0469_checked
#print axioms fusedMap0469_checked
#print axioms certified0469
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
