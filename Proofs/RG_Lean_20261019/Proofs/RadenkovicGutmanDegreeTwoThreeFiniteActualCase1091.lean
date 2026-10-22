/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1091 : Family 7 := level7.get ⟨91,by decide⟩
def sourceMap1091 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,8,9,10,11,5,6,7] (sourceLabel 7 0 2 v)
def fusedMap1091 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap1091_checked : acceptsGraphIso
    (source (graph core1091) (root 7) 0 2) DegreeOneSmallSpectrum818.graph sourceMap1091=true := by decide +kernel
theorem fusedMap1091_checked : acceptsGraphIso
    (fused (graph core1091) (root 7) 0 2) DegreeOneSmallSpectrum536.graph fusedMap1091=true := by decide +kernel
theorem certified1091 : Certified (graph core1091) (root 7) 0 2 :=
  of_native_maps core1091 DegreeOneSmallSpectrum818.graph DegreeOneSmallSpectrum536.graph
    sourceMap1091 fusedMap1091 sourceMap1091_checked fusedMap1091_checked
    DegreeTwoThreeFiniteComparisons.comparison1091
#print axioms sourceMap1091_checked
#print axioms fusedMap1091_checked
#print axioms certified1091
def sourceMap1091swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,8,9,10,5,6,7,11] (sourceLabel 7 2 0 v)
def fusedMap1091swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap1091swap_checked : acceptsGraphIso
    (source (graph core1091) (root 7) 2 0) DegreeOneSmallSpectrum818.graph sourceMap1091swap=true := by decide +kernel
theorem fusedMap1091swap_checked : acceptsGraphIso
    (fused (graph core1091) (root 7) 2 0) DegreeOneSmallSpectrum536.graph fusedMap1091swap=true := by decide +kernel
theorem certified1091swap : Certified (graph core1091) (root 7) 2 0 :=
  of_native_maps core1091 DegreeOneSmallSpectrum818.graph DegreeOneSmallSpectrum536.graph
    sourceMap1091swap fusedMap1091swap sourceMap1091swap_checked fusedMap1091swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1091
#print axioms sourceMap1091swap_checked
#print axioms fusedMap1091swap_checked
#print axioms certified1091swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
