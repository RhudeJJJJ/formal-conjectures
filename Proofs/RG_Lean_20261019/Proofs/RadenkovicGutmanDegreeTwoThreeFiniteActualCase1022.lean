/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1022 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap1022 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 2) → Fin 7 :=
  fun v => ![0,1,2,5,6,3,4] (sourceLabel 3 0 1 v)
def fusedMap1022 : (Vertices 3 ⊕ Fin 3) → Fin 7 :=
  fun v => ![0,1,2,3,4,5,6] (fusedLabel 3 0 1 v)
theorem sourceMap1022_checked : acceptsGraphIso
    (source (graph core1022) (root 3) 0 1) DegreeTwoThreeSpectrum013.graph sourceMap1022=true := by decide +kernel
theorem fusedMap1022_checked : acceptsGraphIso
    (fused (graph core1022) (root 3) 0 1) DegreeOneSmallSpectrum009.graph fusedMap1022=true := by decide +kernel
theorem certified1022 : Certified (graph core1022) (root 3) 0 1 :=
  of_native_maps core1022 DegreeTwoThreeSpectrum013.graph DegreeOneSmallSpectrum009.graph
    sourceMap1022 fusedMap1022 sourceMap1022_checked fusedMap1022_checked
    DegreeTwoThreeFiniteComparisons.comparison1022
#print axioms sourceMap1022_checked
#print axioms fusedMap1022_checked
#print axioms certified1022
def sourceMap1022swap : (Vertices 3 ⊕ Fin 2 ⊕ Fin 1) → Fin 7 :=
  fun v => ![0,1,2,5,3,4,6] (sourceLabel 3 1 0 v)
def fusedMap1022swap : (Vertices 3 ⊕ Fin 3) → Fin 7 :=
  fun v => ![0,1,2,3,4,5,6] (fusedLabel 3 1 0 v)
theorem sourceMap1022swap_checked : acceptsGraphIso
    (source (graph core1022) (root 3) 1 0) DegreeTwoThreeSpectrum013.graph sourceMap1022swap=true := by decide +kernel
theorem fusedMap1022swap_checked : acceptsGraphIso
    (fused (graph core1022) (root 3) 1 0) DegreeOneSmallSpectrum009.graph fusedMap1022swap=true := by decide +kernel
theorem certified1022swap : Certified (graph core1022) (root 3) 1 0 :=
  of_native_maps core1022 DegreeTwoThreeSpectrum013.graph DegreeOneSmallSpectrum009.graph
    sourceMap1022swap fusedMap1022swap sourceMap1022swap_checked fusedMap1022swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1022
#print axioms sourceMap1022swap_checked
#print axioms fusedMap1022swap_checked
#print axioms certified1022swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
