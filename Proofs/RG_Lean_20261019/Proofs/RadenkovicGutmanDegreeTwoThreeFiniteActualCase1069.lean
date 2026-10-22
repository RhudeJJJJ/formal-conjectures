/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1069 : Family 7 := level7.get ⟨41,by decide⟩
def sourceMap1069 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 7 0 2 v)
def fusedMap1069 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (fusedLabel 7 0 2 v)
theorem sourceMap1069_checked : acceptsGraphIso
    (source (graph core1069) (root 7) 0 2) DegreeOneSmallSpectrum516.graph sourceMap1069=true := by decide +kernel
theorem fusedMap1069_checked : acceptsGraphIso
    (fused (graph core1069) (root 7) 0 2) DegreeOneSmallSpectrum518.graph fusedMap1069=true := by decide +kernel
theorem certified1069 : Certified (graph core1069) (root 7) 0 2 :=
  of_native_maps core1069 DegreeOneSmallSpectrum516.graph DegreeOneSmallSpectrum518.graph
    sourceMap1069 fusedMap1069 sourceMap1069_checked fusedMap1069_checked
    DegreeTwoThreeFiniteComparisons.comparison1069
#print axioms sourceMap1069_checked
#print axioms fusedMap1069_checked
#print axioms certified1069
def sourceMap1069swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9,11] (sourceLabel 7 2 0 v)
def fusedMap1069swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (fusedLabel 7 2 0 v)
theorem sourceMap1069swap_checked : acceptsGraphIso
    (source (graph core1069) (root 7) 2 0) DegreeOneSmallSpectrum516.graph sourceMap1069swap=true := by decide +kernel
theorem fusedMap1069swap_checked : acceptsGraphIso
    (fused (graph core1069) (root 7) 2 0) DegreeOneSmallSpectrum518.graph fusedMap1069swap=true := by decide +kernel
theorem certified1069swap : Certified (graph core1069) (root 7) 2 0 :=
  of_native_maps core1069 DegreeOneSmallSpectrum516.graph DegreeOneSmallSpectrum518.graph
    sourceMap1069swap fusedMap1069swap sourceMap1069swap_checked fusedMap1069swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1069
#print axioms sourceMap1069swap_checked
#print axioms fusedMap1069swap_checked
#print axioms certified1069swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
