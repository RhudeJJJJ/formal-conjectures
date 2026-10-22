/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0190 : Family 6 := level6.get ⟨23,by decide⟩
def sourceMap0190 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap0190 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap0190_checked : acceptsGraphIso
    (source (graph core0190) (root 6) 2 4) DegreeOneMiddleResidualSpectrum282.graph sourceMap0190=true := by decide +kernel
theorem fusedMap0190_checked : acceptsGraphIso
    (fused (graph core0190) (root 6) 2 4) DegreeTwoThreeSpectrum2322.graph fusedMap0190=true := by decide +kernel
theorem certified0190 : Certified (graph core0190) (root 6) 2 4 :=
  of_native_maps core0190 DegreeOneMiddleResidualSpectrum282.graph DegreeTwoThreeSpectrum2322.graph
    sourceMap0190 fusedMap0190 sourceMap0190_checked fusedMap0190_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0190
#print axioms sourceMap0190_checked
#print axioms fusedMap0190_checked
#print axioms certified0190
def sourceMap0190swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,11,12,13,14,8,9,10] (sourceLabel 6 4 2 v)
def fusedMap0190swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap0190swap_checked : acceptsGraphIso
    (source (graph core0190) (root 6) 4 2) DegreeOneMiddleResidualSpectrum282.graph sourceMap0190swap=true := by decide +kernel
theorem fusedMap0190swap_checked : acceptsGraphIso
    (fused (graph core0190) (root 6) 4 2) DegreeTwoThreeSpectrum2322.graph fusedMap0190swap=true := by decide +kernel
theorem certified0190swap : Certified (graph core0190) (root 6) 4 2 :=
  of_native_maps core0190 DegreeOneMiddleResidualSpectrum282.graph DegreeTwoThreeSpectrum2322.graph
    sourceMap0190swap fusedMap0190swap sourceMap0190swap_checked fusedMap0190swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0190
#print axioms sourceMap0190swap_checked
#print axioms fusedMap0190swap_checked
#print axioms certified0190swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
