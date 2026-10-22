/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1023 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap1023 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 2) → Fin 8 :=
  fun v => ![0,5,6,7,3,4,1,2] (sourceLabel 4 0 1 v)
def fusedMap1023 : (Vertices 4 ⊕ Fin 3) → Fin 8 :=
  fun v => ![0,1,2,3,7,4,5,6] (fusedLabel 4 0 1 v)
theorem sourceMap1023_checked : acceptsGraphIso
    (source (graph core1023) (root 4) 0 1) DegreeOneSmallSpectrum023.graph sourceMap1023=true := by decide +kernel
theorem fusedMap1023_checked : acceptsGraphIso
    (fused (graph core1023) (root 4) 0 1) DegreeOneSmallSpectrum026.graph fusedMap1023=true := by decide +kernel
theorem certified1023 : Certified (graph core1023) (root 4) 0 1 :=
  of_native_maps core1023 DegreeOneSmallSpectrum023.graph DegreeOneSmallSpectrum026.graph
    sourceMap1023 fusedMap1023 sourceMap1023_checked fusedMap1023_checked
    DegreeTwoThreeFiniteComparisons.comparison1023
#print axioms sourceMap1023_checked
#print axioms fusedMap1023_checked
#print axioms certified1023
def sourceMap1023swap : (Vertices 4 ⊕ Fin 2 ⊕ Fin 1) → Fin 8 :=
  fun v => ![0,5,6,7,3,1,2,4] (sourceLabel 4 1 0 v)
def fusedMap1023swap : (Vertices 4 ⊕ Fin 3) → Fin 8 :=
  fun v => ![0,1,2,3,7,4,5,6] (fusedLabel 4 1 0 v)
theorem sourceMap1023swap_checked : acceptsGraphIso
    (source (graph core1023) (root 4) 1 0) DegreeOneSmallSpectrum023.graph sourceMap1023swap=true := by decide +kernel
theorem fusedMap1023swap_checked : acceptsGraphIso
    (fused (graph core1023) (root 4) 1 0) DegreeOneSmallSpectrum026.graph fusedMap1023swap=true := by decide +kernel
theorem certified1023swap : Certified (graph core1023) (root 4) 1 0 :=
  of_native_maps core1023 DegreeOneSmallSpectrum023.graph DegreeOneSmallSpectrum026.graph
    sourceMap1023swap fusedMap1023swap sourceMap1023swap_checked fusedMap1023swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1023
#print axioms sourceMap1023swap_checked
#print axioms fusedMap1023swap_checked
#print axioms certified1023swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
