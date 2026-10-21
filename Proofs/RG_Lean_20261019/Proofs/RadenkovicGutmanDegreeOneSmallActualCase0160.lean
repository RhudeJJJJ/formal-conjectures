/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0160 : Family 5 := level5.get ⟨0,by decide⟩
def sourceMap0160 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 2) → Fin 9 :=
  fun v => ![1,0,5,6,7,8,4,2,3] (sourceLabel 5 0 1 v)
def fusedMap0160 : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![1,0,5,6,7,8,2,3,4] (fusedLabel 5 0 1 v)
theorem sourceMap0160_checked : acceptsGraphIso
    (source (graph core0160) (root 5) 0 1) DegreeOneSmallSpectrum035.graph sourceMap0160=true := by decide +kernel
theorem fusedMap0160_checked : acceptsGraphIso
    (fused (graph core0160) (root 5) 0 1) DegreeOneSmallSpectrum037.graph fusedMap0160=true := by decide +kernel
theorem certified0160 : Certified (graph core0160) (root 5) 0 1 :=
  of_native_maps core0160 DegreeOneSmallSpectrum035.graph DegreeOneSmallSpectrum037.graph
    sourceMap0160 fusedMap0160 sourceMap0160_checked fusedMap0160_checked
    DegreeOneSmallComparisons.comparison0160
#print axioms sourceMap0160_checked
#print axioms fusedMap0160_checked
#print axioms certified0160
def sourceMap0160swap : (Vertices 5 ⊕ Fin 2 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,5,6,7,8,2,3,4] (sourceLabel 5 1 0 v)
def fusedMap0160swap : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![1,0,5,6,7,8,2,3,4] (fusedLabel 5 1 0 v)
theorem sourceMap0160swap_checked : acceptsGraphIso
    (source (graph core0160) (root 5) 1 0) DegreeOneSmallSpectrum035.graph sourceMap0160swap=true := by decide +kernel
theorem fusedMap0160swap_checked : acceptsGraphIso
    (fused (graph core0160) (root 5) 1 0) DegreeOneSmallSpectrum037.graph fusedMap0160swap=true := by decide +kernel
theorem certified0160swap : Certified (graph core0160) (root 5) 1 0 :=
  of_native_maps core0160 DegreeOneSmallSpectrum035.graph DegreeOneSmallSpectrum037.graph
    sourceMap0160swap fusedMap0160swap sourceMap0160swap_checked fusedMap0160swap_checked
    DegreeOneSmallComparisons.comparison0160
#print axioms sourceMap0160swap_checked
#print axioms fusedMap0160swap_checked
#print axioms certified0160swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
