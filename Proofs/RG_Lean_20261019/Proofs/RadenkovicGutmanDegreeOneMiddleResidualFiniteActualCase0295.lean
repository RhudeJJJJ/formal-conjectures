/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0295 : Family 9 := level9.get ⟨139,by decide⟩
def sourceMap0295 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0295 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0295_checked : acceptsGraphIso
    (source (graph core0295) (root 9) 2 2) DegreeOneMiddleResidualSpectrum747.graph sourceMap0295=true := by decide +kernel
theorem fusedMap0295_checked : acceptsGraphIso
    (fused (graph core0295) (root 9) 2 2) DegreeTwoThreeSpectrum3894.graph fusedMap0295=true := by decide +kernel
theorem certified0295 : Certified (graph core0295) (root 9) 2 2 :=
  of_native_maps core0295 DegreeOneMiddleResidualSpectrum747.graph DegreeTwoThreeSpectrum3894.graph
    sourceMap0295 fusedMap0295 sourceMap0295_checked fusedMap0295_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0295
#print axioms sourceMap0295_checked
#print axioms fusedMap0295_checked
#print axioms certified0295
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
