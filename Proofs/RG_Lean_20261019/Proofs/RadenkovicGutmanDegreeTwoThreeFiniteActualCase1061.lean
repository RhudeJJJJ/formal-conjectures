/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1061 : Family 7 := level7.get ⟨16,by decide⟩
def sourceMap1061 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 7 0 2 v)
def fusedMap1061 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,11,7,8,9,10] (fusedLabel 7 0 2 v)
theorem sourceMap1061_checked : acceptsGraphIso
    (source (graph core1061) (root 7) 0 2) DegreeOneSmallSpectrum557.graph sourceMap1061=true := by decide +kernel
theorem fusedMap1061_checked : acceptsGraphIso
    (fused (graph core1061) (root 7) 0 2) DegreeOneSmallSpectrum385.graph fusedMap1061=true := by decide +kernel
theorem certified1061 : Certified (graph core1061) (root 7) 0 2 :=
  of_native_maps core1061 DegreeOneSmallSpectrum557.graph DegreeOneSmallSpectrum385.graph
    sourceMap1061 fusedMap1061 sourceMap1061_checked fusedMap1061_checked
    DegreeTwoThreeFiniteComparisons.comparison1061
#print axioms sourceMap1061_checked
#print axioms fusedMap1061_checked
#print axioms certified1061
def sourceMap1061swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9,11] (sourceLabel 7 2 0 v)
def fusedMap1061swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,11,7,8,9,10] (fusedLabel 7 2 0 v)
theorem sourceMap1061swap_checked : acceptsGraphIso
    (source (graph core1061) (root 7) 2 0) DegreeOneSmallSpectrum557.graph sourceMap1061swap=true := by decide +kernel
theorem fusedMap1061swap_checked : acceptsGraphIso
    (fused (graph core1061) (root 7) 2 0) DegreeOneSmallSpectrum385.graph fusedMap1061swap=true := by decide +kernel
theorem certified1061swap : Certified (graph core1061) (root 7) 2 0 :=
  of_native_maps core1061 DegreeOneSmallSpectrum557.graph DegreeOneSmallSpectrum385.graph
    sourceMap1061swap fusedMap1061swap sourceMap1061swap_checked fusedMap1061swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1061
#print axioms sourceMap1061swap_checked
#print axioms fusedMap1061swap_checked
#print axioms certified1061swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
