/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1068 : Family 7 := level7.get ⟨37,by decide⟩
def sourceMap1068 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,9,10,11,6,7,8] (sourceLabel 7 0 2 v)
def fusedMap1068 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,10,11,6,7,8,9] (fusedLabel 7 0 2 v)
theorem sourceMap1068_checked : acceptsGraphIso
    (source (graph core1068) (root 7) 0 2) DegreeOneSmallSpectrum493.graph sourceMap1068=true := by decide +kernel
theorem fusedMap1068_checked : acceptsGraphIso
    (fused (graph core1068) (root 7) 0 2) DegreeOneSmallSpectrum498.graph fusedMap1068=true := by decide +kernel
theorem certified1068 : Certified (graph core1068) (root 7) 0 2 :=
  of_native_maps core1068 DegreeOneSmallSpectrum493.graph DegreeOneSmallSpectrum498.graph
    sourceMap1068 fusedMap1068 sourceMap1068_checked fusedMap1068_checked
    DegreeTwoThreeFiniteComparisons.comparison1068
#print axioms sourceMap1068_checked
#print axioms fusedMap1068_checked
#print axioms certified1068
def sourceMap1068swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,9,10,6,7,8,11] (sourceLabel 7 2 0 v)
def fusedMap1068swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,10,11,6,7,8,9] (fusedLabel 7 2 0 v)
theorem sourceMap1068swap_checked : acceptsGraphIso
    (source (graph core1068) (root 7) 2 0) DegreeOneSmallSpectrum493.graph sourceMap1068swap=true := by decide +kernel
theorem fusedMap1068swap_checked : acceptsGraphIso
    (fused (graph core1068) (root 7) 2 0) DegreeOneSmallSpectrum498.graph fusedMap1068swap=true := by decide +kernel
theorem certified1068swap : Certified (graph core1068) (root 7) 2 0 :=
  of_native_maps core1068 DegreeOneSmallSpectrum493.graph DegreeOneSmallSpectrum498.graph
    sourceMap1068swap fusedMap1068swap sourceMap1068swap_checked fusedMap1068swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1068
#print axioms sourceMap1068swap_checked
#print axioms fusedMap1068swap_checked
#print axioms certified1068swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
