/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1087 : Family 7 := level7.get ⟨84,by decide⟩
def sourceMap1087 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,9,10,11,6,7,8] (sourceLabel 7 0 2 v)
def fusedMap1087 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap1087_checked : acceptsGraphIso
    (source (graph core1087) (root 7) 0 2) DegreeOneSmallSpectrum796.graph sourceMap1087=true := by decide +kernel
theorem fusedMap1087_checked : acceptsGraphIso
    (fused (graph core1087) (root 7) 0 2) DegreeOneSmallSpectrum506.graph fusedMap1087=true := by decide +kernel
theorem certified1087 : Certified (graph core1087) (root 7) 0 2 :=
  of_native_maps core1087 DegreeOneSmallSpectrum796.graph DegreeOneSmallSpectrum506.graph
    sourceMap1087 fusedMap1087 sourceMap1087_checked fusedMap1087_checked
    DegreeTwoThreeFiniteComparisons.comparison1087
#print axioms sourceMap1087_checked
#print axioms fusedMap1087_checked
#print axioms certified1087
def sourceMap1087swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,9,10,6,7,8,11] (sourceLabel 7 2 0 v)
def fusedMap1087swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap1087swap_checked : acceptsGraphIso
    (source (graph core1087) (root 7) 2 0) DegreeOneSmallSpectrum796.graph sourceMap1087swap=true := by decide +kernel
theorem fusedMap1087swap_checked : acceptsGraphIso
    (fused (graph core1087) (root 7) 2 0) DegreeOneSmallSpectrum506.graph fusedMap1087swap=true := by decide +kernel
theorem certified1087swap : Certified (graph core1087) (root 7) 2 0 :=
  of_native_maps core1087 DegreeOneSmallSpectrum796.graph DegreeOneSmallSpectrum506.graph
    sourceMap1087swap fusedMap1087swap sourceMap1087swap_checked fusedMap1087swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1087
#print axioms sourceMap1087swap_checked
#print axioms fusedMap1087swap_checked
#print axioms certified1087swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
