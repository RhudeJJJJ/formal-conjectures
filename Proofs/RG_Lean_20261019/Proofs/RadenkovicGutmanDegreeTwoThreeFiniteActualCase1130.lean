/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1130 : Family 8 := level8.get ⟨123,by decide⟩
def sourceMap1130 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1130 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1130_checked : acceptsGraphIso
    (source (graph core1130) (root 8) 0 2) DegreeOneSmallSpectrum1209.graph sourceMap1130=true := by decide +kernel
theorem fusedMap1130_checked : acceptsGraphIso
    (fused (graph core1130) (root 8) 0 2) DegreeOneSmallSpectrum1211.graph fusedMap1130=true := by decide +kernel
theorem certified1130 : Certified (graph core1130) (root 8) 0 2 :=
  of_native_maps core1130 DegreeOneSmallSpectrum1209.graph DegreeOneSmallSpectrum1211.graph
    sourceMap1130 fusedMap1130 sourceMap1130_checked fusedMap1130_checked
    DegreeTwoThreeFiniteComparisons.comparison1130
#print axioms sourceMap1130_checked
#print axioms fusedMap1130_checked
#print axioms certified1130
def sourceMap1130swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1130swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1130swap_checked : acceptsGraphIso
    (source (graph core1130) (root 8) 2 0) DegreeOneSmallSpectrum1209.graph sourceMap1130swap=true := by decide +kernel
theorem fusedMap1130swap_checked : acceptsGraphIso
    (fused (graph core1130) (root 8) 2 0) DegreeOneSmallSpectrum1211.graph fusedMap1130swap=true := by decide +kernel
theorem certified1130swap : Certified (graph core1130) (root 8) 2 0 :=
  of_native_maps core1130 DegreeOneSmallSpectrum1209.graph DegreeOneSmallSpectrum1211.graph
    sourceMap1130swap fusedMap1130swap sourceMap1130swap_checked fusedMap1130swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1130
#print axioms sourceMap1130swap_checked
#print axioms fusedMap1130swap_checked
#print axioms certified1130swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
