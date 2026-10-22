/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0188 : Family 6 := level6.get ⟨20,by decide⟩
def sourceMap0188 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap0188 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap0188_checked : acceptsGraphIso
    (source (graph core0188) (root 6) 2 4) DegreeOneMiddleResidualSpectrum269.graph sourceMap0188=true := by decide +kernel
theorem fusedMap0188_checked : acceptsGraphIso
    (fused (graph core0188) (root 6) 2 4) DegreeTwoThreeSpectrum2315.graph fusedMap0188=true := by decide +kernel
theorem certified0188 : Certified (graph core0188) (root 6) 2 4 :=
  of_native_maps core0188 DegreeOneMiddleResidualSpectrum269.graph DegreeTwoThreeSpectrum2315.graph
    sourceMap0188 fusedMap0188 sourceMap0188_checked fusedMap0188_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0188
#print axioms sourceMap0188_checked
#print axioms fusedMap0188_checked
#print axioms certified0188
def sourceMap0188swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,11,12,13,14,8,9,10] (sourceLabel 6 4 2 v)
def fusedMap0188swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap0188swap_checked : acceptsGraphIso
    (source (graph core0188) (root 6) 4 2) DegreeOneMiddleResidualSpectrum269.graph sourceMap0188swap=true := by decide +kernel
theorem fusedMap0188swap_checked : acceptsGraphIso
    (fused (graph core0188) (root 6) 4 2) DegreeTwoThreeSpectrum2315.graph fusedMap0188swap=true := by decide +kernel
theorem certified0188swap : Certified (graph core0188) (root 6) 4 2 :=
  of_native_maps core0188 DegreeOneMiddleResidualSpectrum269.graph DegreeTwoThreeSpectrum2315.graph
    sourceMap0188swap fusedMap0188swap sourceMap0188swap_checked fusedMap0188swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0188
#print axioms sourceMap0188swap_checked
#print axioms fusedMap0188swap_checked
#print axioms certified0188swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
