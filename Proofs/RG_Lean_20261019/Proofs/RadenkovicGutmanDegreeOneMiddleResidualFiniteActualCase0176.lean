/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0176 : Family 6 := level6.get ⟨2,by decide⟩
def sourceMap0176 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,7,8,9,10,11] (sourceLabel 6 2 4 v)
def fusedMap0176 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap0176_checked : acceptsGraphIso
    (source (graph core0176) (root 6) 2 4) DegreeOneMiddleResidualSpectrum233.graph sourceMap0176=true := by decide +kernel
theorem fusedMap0176_checked : acceptsGraphIso
    (fused (graph core0176) (root 6) 2 4) DegreeTwoThreeSpectrum2310.graph fusedMap0176=true := by decide +kernel
theorem certified0176 : Certified (graph core0176) (root 6) 2 4 :=
  of_native_maps core0176 DegreeOneMiddleResidualSpectrum233.graph DegreeTwoThreeSpectrum2310.graph
    sourceMap0176 fusedMap0176 sourceMap0176_checked fusedMap0176_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0176
#print axioms sourceMap0176_checked
#print axioms fusedMap0176_checked
#print axioms certified0176
def sourceMap0176swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 6 4 2 v)
def fusedMap0176swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap0176swap_checked : acceptsGraphIso
    (source (graph core0176) (root 6) 4 2) DegreeOneMiddleResidualSpectrum233.graph sourceMap0176swap=true := by decide +kernel
theorem fusedMap0176swap_checked : acceptsGraphIso
    (fused (graph core0176) (root 6) 4 2) DegreeTwoThreeSpectrum2310.graph fusedMap0176swap=true := by decide +kernel
theorem certified0176swap : Certified (graph core0176) (root 6) 4 2 :=
  of_native_maps core0176 DegreeOneMiddleResidualSpectrum233.graph DegreeTwoThreeSpectrum2310.graph
    sourceMap0176swap fusedMap0176swap sourceMap0176swap_checked fusedMap0176swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0176
#print axioms sourceMap0176swap_checked
#print axioms fusedMap0176swap_checked
#print axioms certified0176swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
