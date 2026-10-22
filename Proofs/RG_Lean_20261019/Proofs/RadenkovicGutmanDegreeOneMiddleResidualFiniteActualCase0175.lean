/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0175 : Family 6 := level6.get ⟨1,by decide⟩
def sourceMap0175 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,7,8,9,10,11] (sourceLabel 6 2 4 v)
def fusedMap0175 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap0175_checked : acceptsGraphIso
    (source (graph core0175) (root 6) 2 4) DegreeOneMiddleResidualSpectrum207.graph sourceMap0175=true := by decide +kernel
theorem fusedMap0175_checked : acceptsGraphIso
    (fused (graph core0175) (root 6) 2 4) DegreeTwoThreeSpectrum2309.graph fusedMap0175=true := by decide +kernel
theorem certified0175 : Certified (graph core0175) (root 6) 2 4 :=
  of_native_maps core0175 DegreeOneMiddleResidualSpectrum207.graph DegreeTwoThreeSpectrum2309.graph
    sourceMap0175 fusedMap0175 sourceMap0175_checked fusedMap0175_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0175
#print axioms sourceMap0175_checked
#print axioms fusedMap0175_checked
#print axioms certified0175
def sourceMap0175swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 6 4 2 v)
def fusedMap0175swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap0175swap_checked : acceptsGraphIso
    (source (graph core0175) (root 6) 4 2) DegreeOneMiddleResidualSpectrum207.graph sourceMap0175swap=true := by decide +kernel
theorem fusedMap0175swap_checked : acceptsGraphIso
    (fused (graph core0175) (root 6) 4 2) DegreeTwoThreeSpectrum2309.graph fusedMap0175swap=true := by decide +kernel
theorem certified0175swap : Certified (graph core0175) (root 6) 4 2 :=
  of_native_maps core0175 DegreeOneMiddleResidualSpectrum207.graph DegreeTwoThreeSpectrum2309.graph
    sourceMap0175swap fusedMap0175swap sourceMap0175swap_checked fusedMap0175swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0175
#print axioms sourceMap0175swap_checked
#print axioms fusedMap0175swap_checked
#print axioms certified0175swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
