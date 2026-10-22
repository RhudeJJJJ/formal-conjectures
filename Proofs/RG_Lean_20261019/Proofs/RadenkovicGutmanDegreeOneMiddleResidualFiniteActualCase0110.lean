/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0110 : Family 8 := level8.get ⟨71,by decide⟩
def sourceMap0110 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap0110 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0110_checked : acceptsGraphIso
    (source (graph core0110) (root 8) 2 2) DegreeOneMiddleResidualSpectrum328.graph sourceMap0110=true := by decide +kernel
theorem fusedMap0110_checked : acceptsGraphIso
    (fused (graph core0110) (root 8) 2 2) DegreeTwoThreeSpectrum2382.graph fusedMap0110=true := by decide +kernel
theorem certified0110 : Certified (graph core0110) (root 8) 2 2 :=
  of_native_maps core0110 DegreeOneMiddleResidualSpectrum328.graph DegreeTwoThreeSpectrum2382.graph
    sourceMap0110 fusedMap0110 sourceMap0110_checked fusedMap0110_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0110
#print axioms sourceMap0110_checked
#print axioms fusedMap0110_checked
#print axioms certified0110
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
