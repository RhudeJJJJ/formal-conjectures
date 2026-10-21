/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0056 : Family 3 := level3.get ⟨0,by decide⟩
def sourceMap0056 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 2) → Fin 7 :=
  fun v => ![0,4,5,6,3,1,2] (sourceLabel 3 0 1 v)
def fusedMap0056 : (Vertices 3 ⊕ Fin 3) → Fin 7 :=
  fun v => ![0,1,2,3,4,5,6] (fusedLabel 3 0 1 v)
theorem sourceMap0056_checked : acceptsGraphIso
    (source (graph core0056) (root 3) 0 1) DegreeOneSmallSpectrum009.graph sourceMap0056=true := by decide +kernel
theorem fusedMap0056_checked : acceptsGraphIso
    (fused (graph core0056) (root 3) 0 1) DegreeOneSmallSpectrum010.graph fusedMap0056=true := by decide +kernel
theorem certified0056 : Certified (graph core0056) (root 3) 0 1 :=
  of_native_maps core0056 DegreeOneSmallSpectrum009.graph DegreeOneSmallSpectrum010.graph
    sourceMap0056 fusedMap0056 sourceMap0056_checked fusedMap0056_checked
    DegreeOneSmallComparisons.comparison0056
#print axioms sourceMap0056_checked
#print axioms fusedMap0056_checked
#print axioms certified0056
def sourceMap0056swap : (Vertices 3 ⊕ Fin 2 ⊕ Fin 1) → Fin 7 :=
  fun v => ![0,4,5,6,1,2,3] (sourceLabel 3 1 0 v)
def fusedMap0056swap : (Vertices 3 ⊕ Fin 3) → Fin 7 :=
  fun v => ![0,1,2,3,4,5,6] (fusedLabel 3 1 0 v)
theorem sourceMap0056swap_checked : acceptsGraphIso
    (source (graph core0056) (root 3) 1 0) DegreeOneSmallSpectrum009.graph sourceMap0056swap=true := by decide +kernel
theorem fusedMap0056swap_checked : acceptsGraphIso
    (fused (graph core0056) (root 3) 1 0) DegreeOneSmallSpectrum010.graph fusedMap0056swap=true := by decide +kernel
theorem certified0056swap : Certified (graph core0056) (root 3) 1 0 :=
  of_native_maps core0056 DegreeOneSmallSpectrum009.graph DegreeOneSmallSpectrum010.graph
    sourceMap0056swap fusedMap0056swap sourceMap0056swap_checked fusedMap0056swap_checked
    DegreeOneSmallComparisons.comparison0056
#print axioms sourceMap0056swap_checked
#print axioms fusedMap0056swap_checked
#print axioms certified0056swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
