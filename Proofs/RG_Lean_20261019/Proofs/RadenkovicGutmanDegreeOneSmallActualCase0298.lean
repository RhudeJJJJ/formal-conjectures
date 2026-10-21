/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0298 : Family 6 := level6.get ⟨3,by decide⟩
def sourceMap0298 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,12,7,8,9,10,11] (sourceLabel 6 0 4 v)
def fusedMap0298 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap0298_checked : acceptsGraphIso
    (source (graph core0298) (root 6) 0 4) DegreeOneSmallSpectrum966.graph sourceMap0298=true := by decide +kernel
theorem fusedMap0298_checked : acceptsGraphIso
    (fused (graph core0298) (root 6) 0 4) DegreeOneSmallSpectrum858.graph fusedMap0298=true := by decide +kernel
theorem certified0298 : Certified (graph core0298) (root 6) 0 4 :=
  of_native_maps core0298 DegreeOneSmallSpectrum966.graph DegreeOneSmallSpectrum858.graph
    sourceMap0298 fusedMap0298 sourceMap0298_checked fusedMap0298_checked
    DegreeOneSmallComparisons.comparison0298
#print axioms sourceMap0298_checked
#print axioms fusedMap0298_checked
#print axioms certified0298
def sourceMap0298swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 4 0 v)
def fusedMap0298swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap0298swap_checked : acceptsGraphIso
    (source (graph core0298) (root 6) 4 0) DegreeOneSmallSpectrum966.graph sourceMap0298swap=true := by decide +kernel
theorem fusedMap0298swap_checked : acceptsGraphIso
    (fused (graph core0298) (root 6) 4 0) DegreeOneSmallSpectrum858.graph fusedMap0298swap=true := by decide +kernel
theorem certified0298swap : Certified (graph core0298) (root 6) 4 0 :=
  of_native_maps core0298 DegreeOneSmallSpectrum966.graph DegreeOneSmallSpectrum858.graph
    sourceMap0298swap fusedMap0298swap sourceMap0298swap_checked fusedMap0298swap_checked
    DegreeOneSmallComparisons.comparison0298
#print axioms sourceMap0298swap_checked
#print axioms fusedMap0298swap_checked
#print axioms certified0298swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
