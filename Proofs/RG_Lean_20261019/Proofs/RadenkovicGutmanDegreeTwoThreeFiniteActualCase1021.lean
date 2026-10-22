/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1021 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap1021 : (Vertices 2 ⊕ Fin 1 ⊕ Fin 2) → Fin 6 :=
  fun v => ![0,1,2,3,4,5] (sourceLabel 2 0 1 v)
def fusedMap1021 : (Vertices 2 ⊕ Fin 3) → Fin 6 :=
  fun v => ![1,2,3,0,4,5] (fusedLabel 2 0 1 v)
theorem sourceMap1021_checked : acceptsGraphIso
    (source (graph core1021) (root 2) 0 1) DegreeTwoThreeSpectrum002.graph sourceMap1021=true := by decide +kernel
theorem fusedMap1021_checked : acceptsGraphIso
    (fused (graph core1021) (root 2) 0 1) DegreeOneSmallSpectrum006.graph fusedMap1021=true := by decide +kernel
theorem certified1021 : Certified (graph core1021) (root 2) 0 1 :=
  of_native_maps core1021 DegreeTwoThreeSpectrum002.graph DegreeOneSmallSpectrum006.graph
    sourceMap1021 fusedMap1021 sourceMap1021_checked fusedMap1021_checked
    DegreeTwoThreeFiniteComparisons.comparison1021
#print axioms sourceMap1021_checked
#print axioms fusedMap1021_checked
#print axioms certified1021
def sourceMap1021swap : (Vertices 2 ⊕ Fin 2 ⊕ Fin 1) → Fin 6 :=
  fun v => ![0,1,2,4,5,3] (sourceLabel 2 1 0 v)
def fusedMap1021swap : (Vertices 2 ⊕ Fin 3) → Fin 6 :=
  fun v => ![1,2,3,0,4,5] (fusedLabel 2 1 0 v)
theorem sourceMap1021swap_checked : acceptsGraphIso
    (source (graph core1021) (root 2) 1 0) DegreeTwoThreeSpectrum002.graph sourceMap1021swap=true := by decide +kernel
theorem fusedMap1021swap_checked : acceptsGraphIso
    (fused (graph core1021) (root 2) 1 0) DegreeOneSmallSpectrum006.graph fusedMap1021swap=true := by decide +kernel
theorem certified1021swap : Certified (graph core1021) (root 2) 1 0 :=
  of_native_maps core1021 DegreeTwoThreeSpectrum002.graph DegreeOneSmallSpectrum006.graph
    sourceMap1021swap fusedMap1021swap sourceMap1021swap_checked fusedMap1021swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1021
#print axioms sourceMap1021swap_checked
#print axioms fusedMap1021swap_checked
#print axioms certified1021swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
