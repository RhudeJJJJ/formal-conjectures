/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0130 : Family 4 := level4.get ⟨2,by decide⟩
def sourceMap0130 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 4 0 3 v)
def fusedMap0130 : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9] (fusedLabel 4 0 3 v)
theorem sourceMap0130_checked : acceptsGraphIso
    (source (graph core0130) (root 4) 0 3) DegreeOneSmallSpectrum083.graph sourceMap0130=true := by decide +kernel
theorem fusedMap0130_checked : acceptsGraphIso
    (fused (graph core0130) (root 4) 0 3) DegreeOneSmallSpectrum086.graph fusedMap0130=true := by decide +kernel
theorem certified0130 : Certified (graph core0130) (root 4) 0 3 :=
  of_native_maps core0130 DegreeOneSmallSpectrum083.graph DegreeOneSmallSpectrum086.graph
    sourceMap0130 fusedMap0130 sourceMap0130_checked fusedMap0130_checked
    DegreeOneSmallComparisons.comparison0130
#print axioms sourceMap0130_checked
#print axioms fusedMap0130_checked
#print axioms certified0130
def sourceMap0130swap : (Vertices 4 ⊕ Fin 4 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,6,7,8,9,5] (sourceLabel 4 3 0 v)
def fusedMap0130swap : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9] (fusedLabel 4 3 0 v)
theorem sourceMap0130swap_checked : acceptsGraphIso
    (source (graph core0130) (root 4) 3 0) DegreeOneSmallSpectrum083.graph sourceMap0130swap=true := by decide +kernel
theorem fusedMap0130swap_checked : acceptsGraphIso
    (fused (graph core0130) (root 4) 3 0) DegreeOneSmallSpectrum086.graph fusedMap0130swap=true := by decide +kernel
theorem certified0130swap : Certified (graph core0130) (root 4) 3 0 :=
  of_native_maps core0130 DegreeOneSmallSpectrum083.graph DegreeOneSmallSpectrum086.graph
    sourceMap0130swap fusedMap0130swap sourceMap0130swap_checked fusedMap0130swap_checked
    DegreeOneSmallComparisons.comparison0130
#print axioms sourceMap0130swap_checked
#print axioms fusedMap0130swap_checked
#print axioms certified0130swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
