/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1429 : Family 9 := level9.get ⟨693,by decide⟩
def sourceMap1429 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 9 0 2 v)
def fusedMap1429 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1429_checked : acceptsGraphIso
    (source (graph core1429) (root 9) 0 2) DegreeTwoThreeSpectrum2244.graph sourceMap1429=true := by decide +kernel
theorem fusedMap1429_checked : acceptsGraphIso
    (fused (graph core1429) (root 9) 0 2) DegreeTwoThreeSpectrum2245.graph fusedMap1429=true := by decide +kernel
theorem certified1429 : Certified (graph core1429) (root 9) 0 2 :=
  of_native_maps core1429 DegreeTwoThreeSpectrum2244.graph DegreeTwoThreeSpectrum2245.graph
    sourceMap1429 fusedMap1429 sourceMap1429_checked fusedMap1429_checked
    DegreeTwoThreeFiniteComparisons.comparison1429
#print axioms sourceMap1429_checked
#print axioms fusedMap1429_checked
#print axioms certified1429
def sourceMap1429swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,10] (sourceLabel 9 2 0 v)
def fusedMap1429swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1429swap_checked : acceptsGraphIso
    (source (graph core1429) (root 9) 2 0) DegreeTwoThreeSpectrum2244.graph sourceMap1429swap=true := by decide +kernel
theorem fusedMap1429swap_checked : acceptsGraphIso
    (fused (graph core1429) (root 9) 2 0) DegreeTwoThreeSpectrum2245.graph fusedMap1429swap=true := by decide +kernel
theorem certified1429swap : Certified (graph core1429) (root 9) 2 0 :=
  of_native_maps core1429 DegreeTwoThreeSpectrum2244.graph DegreeTwoThreeSpectrum2245.graph
    sourceMap1429swap fusedMap1429swap sourceMap1429swap_checked fusedMap1429swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1429
#print axioms sourceMap1429swap_checked
#print axioms fusedMap1429swap_checked
#print axioms certified1429swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
