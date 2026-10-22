/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0280 : Family 9 := level9.get ⟨108,by decide⟩
def sourceMap0280 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,10,11,12,13,14,15,8,9,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0280 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0280_checked : acceptsGraphIso
    (source (graph core0280) (root 9) 2 2) DegreeOneMiddleResidualSpectrum697.graph sourceMap0280=true := by decide +kernel
theorem fusedMap0280_checked : acceptsGraphIso
    (fused (graph core0280) (root 9) 2 2) DegreeTwoThreeSpectrum4108.graph fusedMap0280=true := by decide +kernel
theorem certified0280 : Certified (graph core0280) (root 9) 2 2 :=
  of_native_maps core0280 DegreeOneMiddleResidualSpectrum697.graph DegreeTwoThreeSpectrum4108.graph
    sourceMap0280 fusedMap0280 sourceMap0280_checked fusedMap0280_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0280
#print axioms sourceMap0280_checked
#print axioms fusedMap0280_checked
#print axioms certified0280
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
