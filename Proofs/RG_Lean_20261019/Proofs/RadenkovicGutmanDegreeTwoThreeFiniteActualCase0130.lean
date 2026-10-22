/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0130 : Family 8 := level8.get ⟨200,by decide⟩
def sourceMap0130 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0130 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0130_checked : acceptsGraphIso
    (source (graph core0130) (root 8) 0 0) DegreeTwoThreeSpectrum320.graph sourceMap0130=true := by decide +kernel
theorem fusedMap0130_checked : acceptsGraphIso
    (fused (graph core0130) (root 8) 0 0) DegreeOneSmallSpectrum252.graph fusedMap0130=true := by decide +kernel
theorem certified0130 : Certified (graph core0130) (root 8) 0 0 :=
  of_native_maps core0130 DegreeTwoThreeSpectrum320.graph DegreeOneSmallSpectrum252.graph
    sourceMap0130 fusedMap0130 sourceMap0130_checked fusedMap0130_checked
    DegreeTwoThreeFiniteComparisons.comparison0130
#print axioms sourceMap0130_checked
#print axioms fusedMap0130_checked
#print axioms certified0130
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
