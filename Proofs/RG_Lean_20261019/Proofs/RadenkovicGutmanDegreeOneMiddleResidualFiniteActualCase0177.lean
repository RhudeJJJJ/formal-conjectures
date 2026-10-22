/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0177 : Family 6 := level6.get ⟨3,by decide⟩
def sourceMap0177 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,7,8,9,10,11] (sourceLabel 6 2 4 v)
def fusedMap0177 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap0177_checked : acceptsGraphIso
    (source (graph core0177) (root 6) 2 4) DegreeOneMiddleResidualSpectrum255.graph sourceMap0177=true := by decide +kernel
theorem fusedMap0177_checked : acceptsGraphIso
    (fused (graph core0177) (root 6) 2 4) DegreeTwoThreeSpectrum2311.graph fusedMap0177=true := by decide +kernel
theorem certified0177 : Certified (graph core0177) (root 6) 2 4 :=
  of_native_maps core0177 DegreeOneMiddleResidualSpectrum255.graph DegreeTwoThreeSpectrum2311.graph
    sourceMap0177 fusedMap0177 sourceMap0177_checked fusedMap0177_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0177
#print axioms sourceMap0177_checked
#print axioms fusedMap0177_checked
#print axioms certified0177
def sourceMap0177swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 6 4 2 v)
def fusedMap0177swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap0177swap_checked : acceptsGraphIso
    (source (graph core0177) (root 6) 4 2) DegreeOneMiddleResidualSpectrum255.graph sourceMap0177swap=true := by decide +kernel
theorem fusedMap0177swap_checked : acceptsGraphIso
    (fused (graph core0177) (root 6) 4 2) DegreeTwoThreeSpectrum2311.graph fusedMap0177swap=true := by decide +kernel
theorem certified0177swap : Certified (graph core0177) (root 6) 4 2 :=
  of_native_maps core0177 DegreeOneMiddleResidualSpectrum255.graph DegreeTwoThreeSpectrum2311.graph
    sourceMap0177swap fusedMap0177swap sourceMap0177swap_checked fusedMap0177swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0177
#print axioms sourceMap0177swap_checked
#print axioms fusedMap0177swap_checked
#print axioms certified0177swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
