/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0182 : Family 6 := level6.get ⟨10,by decide⟩
def sourceMap0182 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap0182 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap0182_checked : acceptsGraphIso
    (source (graph core0182) (root 6) 2 4) DegreeOneMiddleResidualSpectrum215.graph sourceMap0182=true := by decide +kernel
theorem fusedMap0182_checked : acceptsGraphIso
    (fused (graph core0182) (root 6) 2 4) DegreeTwoThreeSpectrum2354.graph fusedMap0182=true := by decide +kernel
theorem certified0182 : Certified (graph core0182) (root 6) 2 4 :=
  of_native_maps core0182 DegreeOneMiddleResidualSpectrum215.graph DegreeTwoThreeSpectrum2354.graph
    sourceMap0182 fusedMap0182 sourceMap0182_checked fusedMap0182_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0182
#print axioms sourceMap0182_checked
#print axioms fusedMap0182_checked
#print axioms certified0182
def sourceMap0182swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,7,8,9] (sourceLabel 6 4 2 v)
def fusedMap0182swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap0182swap_checked : acceptsGraphIso
    (source (graph core0182) (root 6) 4 2) DegreeOneMiddleResidualSpectrum215.graph sourceMap0182swap=true := by decide +kernel
theorem fusedMap0182swap_checked : acceptsGraphIso
    (fused (graph core0182) (root 6) 4 2) DegreeTwoThreeSpectrum2354.graph fusedMap0182swap=true := by decide +kernel
theorem certified0182swap : Certified (graph core0182) (root 6) 4 2 :=
  of_native_maps core0182 DegreeOneMiddleResidualSpectrum215.graph DegreeTwoThreeSpectrum2354.graph
    sourceMap0182swap fusedMap0182swap sourceMap0182swap_checked fusedMap0182swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0182
#print axioms sourceMap0182swap_checked
#print axioms fusedMap0182swap_checked
#print axioms certified0182swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
