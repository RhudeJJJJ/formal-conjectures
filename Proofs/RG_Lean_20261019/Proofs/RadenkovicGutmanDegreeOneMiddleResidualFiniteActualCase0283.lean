/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0283 : Family 9 := level9.get ⟨114,by decide⟩
def sourceMap0283 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0283 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0283_checked : acceptsGraphIso
    (source (graph core0283) (root 9) 2 2) DegreeOneMiddleResidualSpectrum722.graph sourceMap0283=true := by decide +kernel
theorem fusedMap0283_checked : acceptsGraphIso
    (fused (graph core0283) (root 9) 2 2) DegreeTwoThreeSpectrum4127.graph fusedMap0283=true := by decide +kernel
theorem certified0283 : Certified (graph core0283) (root 9) 2 2 :=
  of_native_maps core0283 DegreeOneMiddleResidualSpectrum722.graph DegreeTwoThreeSpectrum4127.graph
    sourceMap0283 fusedMap0283 sourceMap0283_checked fusedMap0283_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0283
#print axioms sourceMap0283_checked
#print axioms fusedMap0283_checked
#print axioms certified0283
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
