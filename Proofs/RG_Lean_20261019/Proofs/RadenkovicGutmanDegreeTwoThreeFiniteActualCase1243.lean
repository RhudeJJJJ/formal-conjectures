/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1243 : Family 9 := level9.get ⟨195,by decide⟩
def sourceMap1243 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,13,10,11,12] (sourceLabel 9 0 2 v)
def fusedMap1243 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,7,8,9,10] (fusedLabel 9 0 2 v)
theorem sourceMap1243_checked : acceptsGraphIso
    (source (graph core1243) (root 9) 0 2) DegreeTwoThreeSpectrum2068.graph sourceMap1243=true := by decide +kernel
theorem fusedMap1243_checked : acceptsGraphIso
    (fused (graph core1243) (root 9) 0 2) DegreeTwoThreeSpectrum1799.graph fusedMap1243=true := by decide +kernel
theorem certified1243 : Certified (graph core1243) (root 9) 0 2 :=
  of_native_maps core1243 DegreeTwoThreeSpectrum2068.graph DegreeTwoThreeSpectrum1799.graph
    sourceMap1243 fusedMap1243 sourceMap1243_checked fusedMap1243_checked
    DegreeTwoThreeFiniteComparisons.comparison1243
#print axioms sourceMap1243_checked
#print axioms fusedMap1243_checked
#print axioms certified1243
def sourceMap1243swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13] (sourceLabel 9 2 0 v)
def fusedMap1243swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,7,8,9,10] (fusedLabel 9 2 0 v)
theorem sourceMap1243swap_checked : acceptsGraphIso
    (source (graph core1243) (root 9) 2 0) DegreeTwoThreeSpectrum2068.graph sourceMap1243swap=true := by decide +kernel
theorem fusedMap1243swap_checked : acceptsGraphIso
    (fused (graph core1243) (root 9) 2 0) DegreeTwoThreeSpectrum1799.graph fusedMap1243swap=true := by decide +kernel
theorem certified1243swap : Certified (graph core1243) (root 9) 2 0 :=
  of_native_maps core1243 DegreeTwoThreeSpectrum2068.graph DegreeTwoThreeSpectrum1799.graph
    sourceMap1243swap fusedMap1243swap sourceMap1243swap_checked fusedMap1243swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1243
#print axioms sourceMap1243swap_checked
#print axioms fusedMap1243swap_checked
#print axioms certified1243swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
