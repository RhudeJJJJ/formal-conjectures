/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0174 : Family 6 := level6.get ⟨0,by decide⟩
def sourceMap0174 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,6,7,8,1,2,3,4,5] (sourceLabel 6 2 4 v)
def fusedMap0174 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap0174_checked : acceptsGraphIso
    (source (graph core0174) (root 6) 2 4) DegreeTwoThreeSpectrum2428.graph sourceMap0174=true := by decide +kernel
theorem fusedMap0174_checked : acceptsGraphIso
    (fused (graph core0174) (root 6) 2 4) DegreeOneMiddleResidualSpectrum111.graph fusedMap0174=true := by decide +kernel
theorem certified0174 : Certified (graph core0174) (root 6) 2 4 :=
  of_native_maps core0174 DegreeTwoThreeSpectrum2428.graph DegreeOneMiddleResidualSpectrum111.graph
    sourceMap0174 fusedMap0174 sourceMap0174_checked fusedMap0174_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0174
#print axioms sourceMap0174_checked
#print axioms fusedMap0174_checked
#print axioms certified0174
def sourceMap0174swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,5,6,7,8] (sourceLabel 6 4 2 v)
def fusedMap0174swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap0174swap_checked : acceptsGraphIso
    (source (graph core0174) (root 6) 4 2) DegreeTwoThreeSpectrum2428.graph sourceMap0174swap=true := by decide +kernel
theorem fusedMap0174swap_checked : acceptsGraphIso
    (fused (graph core0174) (root 6) 4 2) DegreeOneMiddleResidualSpectrum111.graph fusedMap0174swap=true := by decide +kernel
theorem certified0174swap : Certified (graph core0174) (root 6) 4 2 :=
  of_native_maps core0174 DegreeTwoThreeSpectrum2428.graph DegreeOneMiddleResidualSpectrum111.graph
    sourceMap0174swap fusedMap0174swap sourceMap0174swap_checked fusedMap0174swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0174
#print axioms sourceMap0174swap_checked
#print axioms fusedMap0174swap_checked
#print axioms certified0174swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
