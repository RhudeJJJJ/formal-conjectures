/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1025 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap1025 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 2) → Fin 8 :=
  fun v => ![0,1,2,3,4,7,5,6] (sourceLabel 4 0 1 v)
def fusedMap1025 : (Vertices 4 ⊕ Fin 3) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (fusedLabel 4 0 1 v)
theorem sourceMap1025_checked : acceptsGraphIso
    (source (graph core1025) (root 4) 0 1) DegreeTwoThreeSpectrum030.graph sourceMap1025=true := by decide +kernel
theorem fusedMap1025_checked : acceptsGraphIso
    (fused (graph core1025) (root 4) 0 1) DegreeOneSmallSpectrum022.graph fusedMap1025=true := by decide +kernel
theorem certified1025 : Certified (graph core1025) (root 4) 0 1 :=
  of_native_maps core1025 DegreeTwoThreeSpectrum030.graph DegreeOneSmallSpectrum022.graph
    sourceMap1025 fusedMap1025 sourceMap1025_checked fusedMap1025_checked
    DegreeTwoThreeFiniteComparisons.comparison1025
#print axioms sourceMap1025_checked
#print axioms fusedMap1025_checked
#print axioms certified1025
def sourceMap1025swap : (Vertices 4 ⊕ Fin 2 ⊕ Fin 1) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (sourceLabel 4 1 0 v)
def fusedMap1025swap : (Vertices 4 ⊕ Fin 3) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (fusedLabel 4 1 0 v)
theorem sourceMap1025swap_checked : acceptsGraphIso
    (source (graph core1025) (root 4) 1 0) DegreeTwoThreeSpectrum030.graph sourceMap1025swap=true := by decide +kernel
theorem fusedMap1025swap_checked : acceptsGraphIso
    (fused (graph core1025) (root 4) 1 0) DegreeOneSmallSpectrum022.graph fusedMap1025swap=true := by decide +kernel
theorem certified1025swap : Certified (graph core1025) (root 4) 1 0 :=
  of_native_maps core1025 DegreeTwoThreeSpectrum030.graph DegreeOneSmallSpectrum022.graph
    sourceMap1025swap fusedMap1025swap sourceMap1025swap_checked fusedMap1025swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1025
#print axioms sourceMap1025swap_checked
#print axioms fusedMap1025swap_checked
#print axioms certified1025swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
