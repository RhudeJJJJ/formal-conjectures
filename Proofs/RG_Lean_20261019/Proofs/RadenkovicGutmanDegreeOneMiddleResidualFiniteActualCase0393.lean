/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0393 : Family 9 := level9.get ⟨326,by decide⟩
def sourceMap0393 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0393 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0393_checked : acceptsGraphIso
    (source (graph core0393) (root 9) 2 2) DegreeOneMiddleResidualSpectrum746.graph sourceMap0393=true := by decide +kernel
theorem fusedMap0393_checked : acceptsGraphIso
    (fused (graph core0393) (root 9) 2 2) DegreeTwoThreeSpectrum4197.graph fusedMap0393=true := by decide +kernel
theorem certified0393 : Certified (graph core0393) (root 9) 2 2 :=
  of_native_maps core0393 DegreeOneMiddleResidualSpectrum746.graph DegreeTwoThreeSpectrum4197.graph
    sourceMap0393 fusedMap0393 sourceMap0393_checked fusedMap0393_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0393
#print axioms sourceMap0393_checked
#print axioms fusedMap0393_checked
#print axioms certified0393
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
