/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0179 : Family 6 := level6.get ⟨6,by decide⟩
def sourceMap0179 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap0179 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap0179_checked : acceptsGraphIso
    (source (graph core0179) (root 6) 2 4) DegreeOneMiddleResidualSpectrum183.graph sourceMap0179=true := by decide +kernel
theorem fusedMap0179_checked : acceptsGraphIso
    (fused (graph core0179) (root 6) 2 4) DegreeTwoThreeSpectrum2320.graph fusedMap0179=true := by decide +kernel
theorem certified0179 : Certified (graph core0179) (root 6) 2 4 :=
  of_native_maps core0179 DegreeOneMiddleResidualSpectrum183.graph DegreeTwoThreeSpectrum2320.graph
    sourceMap0179 fusedMap0179 sourceMap0179_checked fusedMap0179_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0179
#print axioms sourceMap0179_checked
#print axioms fusedMap0179_checked
#print axioms certified0179
def sourceMap0179swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,7,8,9] (sourceLabel 6 4 2 v)
def fusedMap0179swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap0179swap_checked : acceptsGraphIso
    (source (graph core0179) (root 6) 4 2) DegreeOneMiddleResidualSpectrum183.graph sourceMap0179swap=true := by decide +kernel
theorem fusedMap0179swap_checked : acceptsGraphIso
    (fused (graph core0179) (root 6) 4 2) DegreeTwoThreeSpectrum2320.graph fusedMap0179swap=true := by decide +kernel
theorem certified0179swap : Certified (graph core0179) (root 6) 4 2 :=
  of_native_maps core0179 DegreeOneMiddleResidualSpectrum183.graph DegreeTwoThreeSpectrum2320.graph
    sourceMap0179swap fusedMap0179swap sourceMap0179swap_checked fusedMap0179swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0179
#print axioms sourceMap0179swap_checked
#print axioms fusedMap0179swap_checked
#print axioms certified0179swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
