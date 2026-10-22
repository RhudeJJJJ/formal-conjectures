/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0180 : Family 6 := level6.get ⟨7,by decide⟩
def sourceMap0180 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap0180 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap0180_checked : acceptsGraphIso
    (source (graph core0180) (root 6) 2 4) DegreeOneMiddleResidualSpectrum196.graph sourceMap0180=true := by decide +kernel
theorem fusedMap0180_checked : acceptsGraphIso
    (fused (graph core0180) (root 6) 2 4) DegreeTwoThreeSpectrum2327.graph fusedMap0180=true := by decide +kernel
theorem certified0180 : Certified (graph core0180) (root 6) 2 4 :=
  of_native_maps core0180 DegreeOneMiddleResidualSpectrum196.graph DegreeTwoThreeSpectrum2327.graph
    sourceMap0180 fusedMap0180 sourceMap0180_checked fusedMap0180_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0180
#print axioms sourceMap0180_checked
#print axioms fusedMap0180_checked
#print axioms certified0180
def sourceMap0180swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,7,8,9] (sourceLabel 6 4 2 v)
def fusedMap0180swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap0180swap_checked : acceptsGraphIso
    (source (graph core0180) (root 6) 4 2) DegreeOneMiddleResidualSpectrum196.graph sourceMap0180swap=true := by decide +kernel
theorem fusedMap0180swap_checked : acceptsGraphIso
    (fused (graph core0180) (root 6) 4 2) DegreeTwoThreeSpectrum2327.graph fusedMap0180swap=true := by decide +kernel
theorem certified0180swap : Certified (graph core0180) (root 6) 4 2 :=
  of_native_maps core0180 DegreeOneMiddleResidualSpectrum196.graph DegreeTwoThreeSpectrum2327.graph
    sourceMap0180swap fusedMap0180swap sourceMap0180swap_checked fusedMap0180swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0180
#print axioms sourceMap0180swap_checked
#print axioms fusedMap0180swap_checked
#print axioms certified0180swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
