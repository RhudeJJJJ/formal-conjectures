/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1066 : Family 7 := level7.get ⟨33,by decide⟩
def sourceMap1066 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 7 0 2 v)
def fusedMap1066 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (fusedLabel 7 0 2 v)
theorem sourceMap1066_checked : acceptsGraphIso
    (source (graph core1066) (root 7) 0 2) DegreeOneSmallSpectrum455.graph sourceMap1066=true := by decide +kernel
theorem fusedMap1066_checked : acceptsGraphIso
    (fused (graph core1066) (root 7) 0 2) DegreeOneSmallSpectrum457.graph fusedMap1066=true := by decide +kernel
theorem certified1066 : Certified (graph core1066) (root 7) 0 2 :=
  of_native_maps core1066 DegreeOneSmallSpectrum455.graph DegreeOneSmallSpectrum457.graph
    sourceMap1066 fusedMap1066 sourceMap1066_checked fusedMap1066_checked
    DegreeTwoThreeFiniteComparisons.comparison1066
#print axioms sourceMap1066_checked
#print axioms fusedMap1066_checked
#print axioms certified1066
def sourceMap1066swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9,11] (sourceLabel 7 2 0 v)
def fusedMap1066swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (fusedLabel 7 2 0 v)
theorem sourceMap1066swap_checked : acceptsGraphIso
    (source (graph core1066) (root 7) 2 0) DegreeOneSmallSpectrum455.graph sourceMap1066swap=true := by decide +kernel
theorem fusedMap1066swap_checked : acceptsGraphIso
    (fused (graph core1066) (root 7) 2 0) DegreeOneSmallSpectrum457.graph fusedMap1066swap=true := by decide +kernel
theorem certified1066swap : Certified (graph core1066) (root 7) 2 0 :=
  of_native_maps core1066 DegreeOneSmallSpectrum455.graph DegreeOneSmallSpectrum457.graph
    sourceMap1066swap fusedMap1066swap sourceMap1066swap_checked fusedMap1066swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1066
#print axioms sourceMap1066swap_checked
#print axioms fusedMap1066swap_checked
#print axioms certified1066swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
