/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1044 : Family 6 := level6.get ⟨9,by decide⟩
def sourceMap1044 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,9,10,6,7,8] (sourceLabel 6 0 2 v)
def fusedMap1044 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,10,6,7,8,9] (fusedLabel 6 0 2 v)
theorem sourceMap1044_checked : acceptsGraphIso
    (source (graph core1044) (root 6) 0 2) DegreeOneSmallSpectrum195.graph sourceMap1044=true := by decide +kernel
theorem fusedMap1044_checked : acceptsGraphIso
    (fused (graph core1044) (root 6) 0 2) DegreeOneSmallSpectrum197.graph fusedMap1044=true := by decide +kernel
theorem certified1044 : Certified (graph core1044) (root 6) 0 2 :=
  of_native_maps core1044 DegreeOneSmallSpectrum195.graph DegreeOneSmallSpectrum197.graph
    sourceMap1044 fusedMap1044 sourceMap1044_checked fusedMap1044_checked
    DegreeTwoThreeFiniteComparisons.comparison1044
#print axioms sourceMap1044_checked
#print axioms fusedMap1044_checked
#print axioms certified1044
def sourceMap1044swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,9,6,7,8,10] (sourceLabel 6 2 0 v)
def fusedMap1044swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,10,6,7,8,9] (fusedLabel 6 2 0 v)
theorem sourceMap1044swap_checked : acceptsGraphIso
    (source (graph core1044) (root 6) 2 0) DegreeOneSmallSpectrum195.graph sourceMap1044swap=true := by decide +kernel
theorem fusedMap1044swap_checked : acceptsGraphIso
    (fused (graph core1044) (root 6) 2 0) DegreeOneSmallSpectrum197.graph fusedMap1044swap=true := by decide +kernel
theorem certified1044swap : Certified (graph core1044) (root 6) 2 0 :=
  of_native_maps core1044 DegreeOneSmallSpectrum195.graph DegreeOneSmallSpectrum197.graph
    sourceMap1044swap fusedMap1044swap sourceMap1044swap_checked fusedMap1044swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1044
#print axioms sourceMap1044swap_checked
#print axioms fusedMap1044swap_checked
#print axioms certified1044swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
