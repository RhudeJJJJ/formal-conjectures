/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0291 : Family 6 := level6.get ⟨2,by decide⟩
def sourceMap0291 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 6 1 2 v)
def fusedMap0291 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap0291_checked : acceptsGraphIso
    (source (graph core0291) (root 6) 1 2) DegreeOneSmallSpectrum555.graph sourceMap0291=true := by decide +kernel
theorem fusedMap0291_checked : acceptsGraphIso
    (fused (graph core0291) (root 6) 1 2) DegreeOneSmallSpectrum386.graph fusedMap0291=true := by decide +kernel
theorem certified0291 : Certified (graph core0291) (root 6) 1 2 :=
  of_native_maps core0291 DegreeOneSmallSpectrum555.graph DegreeOneSmallSpectrum386.graph
    sourceMap0291 fusedMap0291 sourceMap0291_checked fusedMap0291_checked
    DegreeOneSmallComparisons.comparison0291
#print axioms sourceMap0291_checked
#print axioms fusedMap0291_checked
#print axioms certified0291
def sourceMap0291swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 6 2 1 v)
def fusedMap0291swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap0291swap_checked : acceptsGraphIso
    (source (graph core0291) (root 6) 2 1) DegreeOneSmallSpectrum555.graph sourceMap0291swap=true := by decide +kernel
theorem fusedMap0291swap_checked : acceptsGraphIso
    (fused (graph core0291) (root 6) 2 1) DegreeOneSmallSpectrum386.graph fusedMap0291swap=true := by decide +kernel
theorem certified0291swap : Certified (graph core0291) (root 6) 2 1 :=
  of_native_maps core0291 DegreeOneSmallSpectrum555.graph DegreeOneSmallSpectrum386.graph
    sourceMap0291swap fusedMap0291swap sourceMap0291swap_checked fusedMap0291swap_checked
    DegreeOneSmallComparisons.comparison0291
#print axioms sourceMap0291swap_checked
#print axioms fusedMap0291swap_checked
#print axioms certified0291swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
