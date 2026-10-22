/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0425 : Family 9 := level9.get ⟨393,by decide⟩
def sourceMap0425 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0425 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0425_checked : acceptsGraphIso
    (source (graph core0425) (root 9) 2 2) DegreeOneMiddleResidualSpectrum803.graph sourceMap0425=true := by decide +kernel
theorem fusedMap0425_checked : acceptsGraphIso
    (fused (graph core0425) (root 9) 2 2) DegreeTwoThreeSpectrum4346.graph fusedMap0425=true := by decide +kernel
theorem certified0425 : Certified (graph core0425) (root 9) 2 2 :=
  of_native_maps core0425 DegreeOneMiddleResidualSpectrum803.graph DegreeTwoThreeSpectrum4346.graph
    sourceMap0425 fusedMap0425 sourceMap0425_checked fusedMap0425_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0425
#print axioms sourceMap0425_checked
#print axioms fusedMap0425_checked
#print axioms certified0425
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
