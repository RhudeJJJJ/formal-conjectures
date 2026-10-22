/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0470 : Family 9 := level9.get ⟨562,by decide⟩
def sourceMap0470 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0470 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0470_checked : acceptsGraphIso
    (source (graph core0470) (root 9) 2 2) DegreeOneMiddleResidualSpectrum914.graph sourceMap0470=true := by decide +kernel
theorem fusedMap0470_checked : acceptsGraphIso
    (fused (graph core0470) (root 9) 2 2) DegreeTwoThreeSpectrum4205.graph fusedMap0470=true := by decide +kernel
theorem certified0470 : Certified (graph core0470) (root 9) 2 2 :=
  of_native_maps core0470 DegreeOneMiddleResidualSpectrum914.graph DegreeTwoThreeSpectrum4205.graph
    sourceMap0470 fusedMap0470 sourceMap0470_checked fusedMap0470_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0470
#print axioms sourceMap0470_checked
#print axioms fusedMap0470_checked
#print axioms certified0470
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
