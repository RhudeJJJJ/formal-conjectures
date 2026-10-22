/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0400 : Family 9 := level9.get ⟨338,by decide⟩
def sourceMap0400 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0400 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0400_checked : acceptsGraphIso
    (source (graph core0400) (root 9) 2 2) DegreeOneMiddleResidualSpectrum757.graph sourceMap0400=true := by decide +kernel
theorem fusedMap0400_checked : acceptsGraphIso
    (fused (graph core0400) (root 9) 2 2) DegreeTwoThreeSpectrum4226.graph fusedMap0400=true := by decide +kernel
theorem certified0400 : Certified (graph core0400) (root 9) 2 2 :=
  of_native_maps core0400 DegreeOneMiddleResidualSpectrum757.graph DegreeTwoThreeSpectrum4226.graph
    sourceMap0400 fusedMap0400 sourceMap0400_checked fusedMap0400_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0400
#print axioms sourceMap0400_checked
#print axioms fusedMap0400_checked
#print axioms certified0400
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
