/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0192 : Family 6 := level6.get ⟨29,by decide⟩
def sourceMap0192 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap0192 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap0192_checked : acceptsGraphIso
    (source (graph core0192) (root 6) 2 4) DegreeOneMiddleResidualSpectrum308.graph sourceMap0192=true := by decide +kernel
theorem fusedMap0192_checked : acceptsGraphIso
    (fused (graph core0192) (root 6) 2 4) DegreeOneMiddleResidualSpectrum134.graph fusedMap0192=true := by decide +kernel
theorem certified0192 : Certified (graph core0192) (root 6) 2 4 :=
  of_native_maps core0192 DegreeOneMiddleResidualSpectrum308.graph DegreeOneMiddleResidualSpectrum134.graph
    sourceMap0192 fusedMap0192 sourceMap0192_checked fusedMap0192_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0192
#print axioms sourceMap0192_checked
#print axioms fusedMap0192_checked
#print axioms certified0192
def sourceMap0192swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,11,12,13,14,8,9,10] (sourceLabel 6 4 2 v)
def fusedMap0192swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap0192swap_checked : acceptsGraphIso
    (source (graph core0192) (root 6) 4 2) DegreeOneMiddleResidualSpectrum308.graph sourceMap0192swap=true := by decide +kernel
theorem fusedMap0192swap_checked : acceptsGraphIso
    (fused (graph core0192) (root 6) 4 2) DegreeOneMiddleResidualSpectrum134.graph fusedMap0192swap=true := by decide +kernel
theorem certified0192swap : Certified (graph core0192) (root 6) 4 2 :=
  of_native_maps core0192 DegreeOneMiddleResidualSpectrum308.graph DegreeOneMiddleResidualSpectrum134.graph
    sourceMap0192swap fusedMap0192swap sourceMap0192swap_checked fusedMap0192swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0192
#print axioms sourceMap0192swap_checked
#print axioms fusedMap0192swap_checked
#print axioms certified0192swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
