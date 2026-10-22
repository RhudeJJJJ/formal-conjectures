/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0370 : Family 9 := level9.get ⟨268,by decide⟩
def sourceMap0370 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0370 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0370_checked : acceptsGraphIso
    (source (graph core0370) (root 9) 2 2) DegreeOneMiddleResidualSpectrum890.graph sourceMap0370=true := by decide +kernel
theorem fusedMap0370_checked : acceptsGraphIso
    (fused (graph core0370) (root 9) 2 2) DegreeTwoThreeSpectrum4081.graph fusedMap0370=true := by decide +kernel
theorem certified0370 : Certified (graph core0370) (root 9) 2 2 :=
  of_native_maps core0370 DegreeOneMiddleResidualSpectrum890.graph DegreeTwoThreeSpectrum4081.graph
    sourceMap0370 fusedMap0370 sourceMap0370_checked fusedMap0370_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0370
#print axioms sourceMap0370_checked
#print axioms fusedMap0370_checked
#print axioms certified0370
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
