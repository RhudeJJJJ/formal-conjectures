/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0413 : Family 9 := level9.get ⟨367,by decide⟩
def sourceMap0413 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0413 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0413_checked : acceptsGraphIso
    (source (graph core0413) (root 9) 2 2) DegreeOneMiddleResidualSpectrum781.graph sourceMap0413=true := by decide +kernel
theorem fusedMap0413_checked : acceptsGraphIso
    (fused (graph core0413) (root 9) 2 2) DegreeTwoThreeSpectrum4289.graph fusedMap0413=true := by decide +kernel
theorem certified0413 : Certified (graph core0413) (root 9) 2 2 :=
  of_native_maps core0413 DegreeOneMiddleResidualSpectrum781.graph DegreeTwoThreeSpectrum4289.graph
    sourceMap0413 fusedMap0413 sourceMap0413_checked fusedMap0413_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0413
#print axioms sourceMap0413_checked
#print axioms fusedMap0413_checked
#print axioms certified0413
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
