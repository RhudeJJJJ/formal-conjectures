/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0407 : Family 9 := level9.get ⟨357,by decide⟩
def sourceMap0407 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0407 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0407_checked : acceptsGraphIso
    (source (graph core0407) (root 9) 2 2) DegreeOneMiddleResidualSpectrum772.graph sourceMap0407=true := by decide +kernel
theorem fusedMap0407_checked : acceptsGraphIso
    (fused (graph core0407) (root 9) 2 2) DegreeTwoThreeSpectrum4268.graph fusedMap0407=true := by decide +kernel
theorem certified0407 : Certified (graph core0407) (root 9) 2 2 :=
  of_native_maps core0407 DegreeOneMiddleResidualSpectrum772.graph DegreeTwoThreeSpectrum4268.graph
    sourceMap0407 fusedMap0407 sourceMap0407_checked fusedMap0407_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0407
#print axioms sourceMap0407_checked
#print axioms fusedMap0407_checked
#print axioms certified0407
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
