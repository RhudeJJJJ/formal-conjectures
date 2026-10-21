/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0289 : Family 6 := level6.get ⟨2,by decide⟩
def sourceMap0289 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,12,7,8,9,10,11] (sourceLabel 6 0 4 v)
def fusedMap0289 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap0289_checked : acceptsGraphIso
    (source (graph core0289) (root 6) 0 4) DegreeOneSmallSpectrum944.graph sourceMap0289=true := by decide +kernel
theorem fusedMap0289_checked : acceptsGraphIso
    (fused (graph core0289) (root 6) 0 4) DegreeOneSmallSpectrum857.graph fusedMap0289=true := by decide +kernel
theorem certified0289 : Certified (graph core0289) (root 6) 0 4 :=
  of_native_maps core0289 DegreeOneSmallSpectrum944.graph DegreeOneSmallSpectrum857.graph
    sourceMap0289 fusedMap0289 sourceMap0289_checked fusedMap0289_checked
    DegreeOneSmallComparisons.comparison0289
#print axioms sourceMap0289_checked
#print axioms fusedMap0289_checked
#print axioms certified0289
def sourceMap0289swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 4 0 v)
def fusedMap0289swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap0289swap_checked : acceptsGraphIso
    (source (graph core0289) (root 6) 4 0) DegreeOneSmallSpectrum944.graph sourceMap0289swap=true := by decide +kernel
theorem fusedMap0289swap_checked : acceptsGraphIso
    (fused (graph core0289) (root 6) 4 0) DegreeOneSmallSpectrum857.graph fusedMap0289swap=true := by decide +kernel
theorem certified0289swap : Certified (graph core0289) (root 6) 4 0 :=
  of_native_maps core0289 DegreeOneSmallSpectrum944.graph DegreeOneSmallSpectrum857.graph
    sourceMap0289swap fusedMap0289swap sourceMap0289swap_checked fusedMap0289swap_checked
    DegreeOneSmallComparisons.comparison0289
#print axioms sourceMap0289swap_checked
#print axioms fusedMap0289swap_checked
#print axioms certified0289swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
