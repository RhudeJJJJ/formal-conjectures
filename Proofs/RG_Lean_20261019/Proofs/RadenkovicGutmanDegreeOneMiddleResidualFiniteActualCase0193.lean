/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0193 : Family 6 := level6.get ⟨37,by decide⟩
def sourceMap0193 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,5,6,7,8,9,10,2,3,4,0,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap0193 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap0193_checked : acceptsGraphIso
    (source (graph core0193) (root 6) 2 4) DegreeOneMiddleResidualSpectrum342.graph sourceMap0193=true := by decide +kernel
theorem fusedMap0193_checked : acceptsGraphIso
    (fused (graph core0193) (root 6) 2 4) DegreeOneMiddleResidualSpectrum170.graph fusedMap0193=true := by decide +kernel
theorem certified0193 : Certified (graph core0193) (root 6) 2 4 :=
  of_native_maps core0193 DegreeOneMiddleResidualSpectrum342.graph DegreeOneMiddleResidualSpectrum170.graph
    sourceMap0193 fusedMap0193 sourceMap0193_checked fusedMap0193_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0193
#print axioms sourceMap0193_checked
#print axioms fusedMap0193_checked
#print axioms certified0193
def sourceMap0193swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,5,6,7,8,9,10,0,11,12,13,14,2,3,4] (sourceLabel 6 4 2 v)
def fusedMap0193swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap0193swap_checked : acceptsGraphIso
    (source (graph core0193) (root 6) 4 2) DegreeOneMiddleResidualSpectrum342.graph sourceMap0193swap=true := by decide +kernel
theorem fusedMap0193swap_checked : acceptsGraphIso
    (fused (graph core0193) (root 6) 4 2) DegreeOneMiddleResidualSpectrum170.graph fusedMap0193swap=true := by decide +kernel
theorem certified0193swap : Certified (graph core0193) (root 6) 4 2 :=
  of_native_maps core0193 DegreeOneMiddleResidualSpectrum342.graph DegreeOneMiddleResidualSpectrum170.graph
    sourceMap0193swap fusedMap0193swap sourceMap0193swap_checked fusedMap0193swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0193
#print axioms sourceMap0193swap_checked
#print axioms fusedMap0193swap_checked
#print axioms certified0193swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
