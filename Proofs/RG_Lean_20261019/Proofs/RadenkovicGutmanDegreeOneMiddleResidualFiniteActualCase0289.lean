/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0289 : Family 9 := level9.get ⟨125,by decide⟩
def sourceMap0289 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,11,12,13,14,15,8,9,10,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0289 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0289_checked : acceptsGraphIso
    (source (graph core0289) (root 9) 2 2) DegreeOneMiddleResidualSpectrum690.graph sourceMap0289=true := by decide +kernel
theorem fusedMap0289_checked : acceptsGraphIso
    (fused (graph core0289) (root 9) 2 2) DegreeTwoThreeSpectrum4154.graph fusedMap0289=true := by decide +kernel
theorem certified0289 : Certified (graph core0289) (root 9) 2 2 :=
  of_native_maps core0289 DegreeOneMiddleResidualSpectrum690.graph DegreeTwoThreeSpectrum4154.graph
    sourceMap0289 fusedMap0289 sourceMap0289_checked fusedMap0289_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0289
#print axioms sourceMap0289_checked
#print axioms fusedMap0289_checked
#print axioms certified0289
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
