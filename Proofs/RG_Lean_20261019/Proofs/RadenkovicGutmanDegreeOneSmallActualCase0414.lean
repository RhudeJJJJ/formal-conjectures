/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0414 : Family 6 := level6.get ⟨23,by decide⟩
def sourceMap0414 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 6 0 3 v)
def fusedMap0414 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap0414_checked : acceptsGraphIso
    (source (graph core0414) (root 6) 0 3) DegreeOneSmallSpectrum436.graph sourceMap0414=true := by decide +kernel
theorem fusedMap0414_checked : acceptsGraphIso
    (fused (graph core0414) (root 6) 0 3) DegreeOneSmallSpectrum440.graph fusedMap0414=true := by decide +kernel
theorem certified0414 : Certified (graph core0414) (root 6) 0 3 :=
  of_native_maps core0414 DegreeOneSmallSpectrum436.graph DegreeOneSmallSpectrum440.graph
    sourceMap0414 fusedMap0414 sourceMap0414_checked fusedMap0414_checked
    DegreeOneSmallComparisons.comparison0414
#print axioms sourceMap0414_checked
#print axioms fusedMap0414_checked
#print axioms certified0414
def sourceMap0414swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,11,7] (sourceLabel 6 3 0 v)
def fusedMap0414swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap0414swap_checked : acceptsGraphIso
    (source (graph core0414) (root 6) 3 0) DegreeOneSmallSpectrum436.graph sourceMap0414swap=true := by decide +kernel
theorem fusedMap0414swap_checked : acceptsGraphIso
    (fused (graph core0414) (root 6) 3 0) DegreeOneSmallSpectrum440.graph fusedMap0414swap=true := by decide +kernel
theorem certified0414swap : Certified (graph core0414) (root 6) 3 0 :=
  of_native_maps core0414 DegreeOneSmallSpectrum436.graph DegreeOneSmallSpectrum440.graph
    sourceMap0414swap fusedMap0414swap sourceMap0414swap_checked fusedMap0414swap_checked
    DegreeOneSmallComparisons.comparison0414
#print axioms sourceMap0414swap_checked
#print axioms fusedMap0414swap_checked
#print axioms certified0414swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
