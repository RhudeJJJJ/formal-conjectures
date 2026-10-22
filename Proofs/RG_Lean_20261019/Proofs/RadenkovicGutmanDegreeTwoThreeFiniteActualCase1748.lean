/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1748 : Family 10 := level10.get ⟨998,by decide⟩
def sourceMap1748 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1748 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1748_checked : acceptsGraphIso
    (source (graph core1748) (root 10) 0 2) DegreeTwoThreeSpectrum3002.graph sourceMap1748=true := by decide +kernel
theorem fusedMap1748_checked : acceptsGraphIso
    (fused (graph core1748) (root 10) 0 2) DegreeTwoThreeSpectrum3003.graph fusedMap1748=true := by decide +kernel
theorem certified1748 : Certified (graph core1748) (root 10) 0 2 :=
  of_native_maps core1748 DegreeTwoThreeSpectrum3002.graph DegreeTwoThreeSpectrum3003.graph
    sourceMap1748 fusedMap1748 sourceMap1748_checked fusedMap1748_checked
    DegreeTwoThreeFiniteComparisons.comparison1748
#print axioms sourceMap1748_checked
#print axioms fusedMap1748_checked
#print axioms certified1748
def sourceMap1748swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1748swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1748swap_checked : acceptsGraphIso
    (source (graph core1748) (root 10) 2 0) DegreeTwoThreeSpectrum3002.graph sourceMap1748swap=true := by decide +kernel
theorem fusedMap1748swap_checked : acceptsGraphIso
    (fused (graph core1748) (root 10) 2 0) DegreeTwoThreeSpectrum3003.graph fusedMap1748swap=true := by decide +kernel
theorem certified1748swap : Certified (graph core1748) (root 10) 2 0 :=
  of_native_maps core1748 DegreeTwoThreeSpectrum3002.graph DegreeTwoThreeSpectrum3003.graph
    sourceMap1748swap fusedMap1748swap sourceMap1748swap_checked fusedMap1748swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1748
#print axioms sourceMap1748swap_checked
#print axioms fusedMap1748swap_checked
#print axioms certified1748swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
