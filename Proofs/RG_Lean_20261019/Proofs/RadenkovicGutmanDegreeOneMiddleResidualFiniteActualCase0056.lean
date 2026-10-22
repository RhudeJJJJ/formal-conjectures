/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0056 : Family 5 := level5.get ⟨13,by decide⟩
def sourceMap0056 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,5,6,7,8,9,2,3,4,0,10,11,12,13] (sourceLabel 5 2 4 v)
def fusedMap0056 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13] (fusedLabel 5 2 4 v)
theorem sourceMap0056_checked : acceptsGraphIso
    (source (graph core0056) (root 5) 2 4) DegreeOneMiddleResidualSpectrum093.graph sourceMap0056=true := by decide +kernel
theorem fusedMap0056_checked : acceptsGraphIso
    (fused (graph core0056) (root 5) 2 4) DegreeOneMiddleResidualSpectrum021.graph fusedMap0056=true := by decide +kernel
theorem certified0056 : Certified (graph core0056) (root 5) 2 4 :=
  of_native_maps core0056 DegreeOneMiddleResidualSpectrum093.graph DegreeOneMiddleResidualSpectrum021.graph
    sourceMap0056 fusedMap0056 sourceMap0056_checked fusedMap0056_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0056
#print axioms sourceMap0056_checked
#print axioms fusedMap0056_checked
#print axioms certified0056
def sourceMap0056swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,5,6,7,8,9,0,10,11,12,13,2,3,4] (sourceLabel 5 4 2 v)
def fusedMap0056swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13] (fusedLabel 5 4 2 v)
theorem sourceMap0056swap_checked : acceptsGraphIso
    (source (graph core0056) (root 5) 4 2) DegreeOneMiddleResidualSpectrum093.graph sourceMap0056swap=true := by decide +kernel
theorem fusedMap0056swap_checked : acceptsGraphIso
    (fused (graph core0056) (root 5) 4 2) DegreeOneMiddleResidualSpectrum021.graph fusedMap0056swap=true := by decide +kernel
theorem certified0056swap : Certified (graph core0056) (root 5) 4 2 :=
  of_native_maps core0056 DegreeOneMiddleResidualSpectrum093.graph DegreeOneMiddleResidualSpectrum021.graph
    sourceMap0056swap fusedMap0056swap sourceMap0056swap_checked fusedMap0056swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0056
#print axioms sourceMap0056swap_checked
#print axioms fusedMap0056swap_checked
#print axioms certified0056swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
