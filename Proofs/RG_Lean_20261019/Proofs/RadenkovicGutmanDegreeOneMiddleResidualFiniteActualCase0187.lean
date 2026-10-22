/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0187 : Family 6 := level6.get ⟨19,by decide⟩
def sourceMap0187 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap0187 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap0187_checked : acceptsGraphIso
    (source (graph core0187) (root 6) 2 4) DegreeOneMiddleResidualSpectrum264.graph sourceMap0187=true := by decide +kernel
theorem fusedMap0187_checked : acceptsGraphIso
    (fused (graph core0187) (root 6) 2 4) DegreeOneMiddleResidualSpectrum112.graph fusedMap0187=true := by decide +kernel
theorem certified0187 : Certified (graph core0187) (root 6) 2 4 :=
  of_native_maps core0187 DegreeOneMiddleResidualSpectrum264.graph DegreeOneMiddleResidualSpectrum112.graph
    sourceMap0187 fusedMap0187 sourceMap0187_checked fusedMap0187_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0187
#print axioms sourceMap0187_checked
#print axioms fusedMap0187_checked
#print axioms certified0187
def sourceMap0187swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,11,12,13,14,8,9,10] (sourceLabel 6 4 2 v)
def fusedMap0187swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap0187swap_checked : acceptsGraphIso
    (source (graph core0187) (root 6) 4 2) DegreeOneMiddleResidualSpectrum264.graph sourceMap0187swap=true := by decide +kernel
theorem fusedMap0187swap_checked : acceptsGraphIso
    (fused (graph core0187) (root 6) 4 2) DegreeOneMiddleResidualSpectrum112.graph fusedMap0187swap=true := by decide +kernel
theorem certified0187swap : Certified (graph core0187) (root 6) 4 2 :=
  of_native_maps core0187 DegreeOneMiddleResidualSpectrum264.graph DegreeOneMiddleResidualSpectrum112.graph
    sourceMap0187swap fusedMap0187swap sourceMap0187swap_checked fusedMap0187swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0187
#print axioms sourceMap0187swap_checked
#print axioms fusedMap0187swap_checked
#print axioms certified0187swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
