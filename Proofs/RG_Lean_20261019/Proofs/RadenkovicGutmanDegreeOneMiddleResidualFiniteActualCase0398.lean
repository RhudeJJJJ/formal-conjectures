/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0398 : Family 9 := level9.get ⟨335,by decide⟩
def sourceMap0398 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0398 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0398_checked : acceptsGraphIso
    (source (graph core0398) (root 9) 2 2) DegreeOneMiddleResidualSpectrum754.graph sourceMap0398=true := by decide +kernel
theorem fusedMap0398_checked : acceptsGraphIso
    (fused (graph core0398) (root 9) 2 2) DegreeTwoThreeSpectrum4219.graph fusedMap0398=true := by decide +kernel
theorem certified0398 : Certified (graph core0398) (root 9) 2 2 :=
  of_native_maps core0398 DegreeOneMiddleResidualSpectrum754.graph DegreeTwoThreeSpectrum4219.graph
    sourceMap0398 fusedMap0398 sourceMap0398_checked fusedMap0398_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0398
#print axioms sourceMap0398_checked
#print axioms fusedMap0398_checked
#print axioms certified0398
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
