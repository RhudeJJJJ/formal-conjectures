/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1195 : Family 9 := level9.get ⟨28,by decide⟩
def sourceMap1195 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![2,1,0,8,9,10,11,12,13,6,7,3,4,5] (sourceLabel 9 0 2 v)
def fusedMap1195 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1195_checked : acceptsGraphIso
    (source (graph core1195) (root 9) 0 2) DegreeTwoThreeSpectrum1885.graph sourceMap1195=true := by decide +kernel
theorem fusedMap1195_checked : acceptsGraphIso
    (fused (graph core1195) (root 9) 0 2) DegreeTwoThreeSpectrum1727.graph fusedMap1195=true := by decide +kernel
theorem certified1195 : Certified (graph core1195) (root 9) 0 2 :=
  of_native_maps core1195 DegreeTwoThreeSpectrum1885.graph DegreeTwoThreeSpectrum1727.graph
    sourceMap1195 fusedMap1195 sourceMap1195_checked fusedMap1195_checked
    DegreeTwoThreeFiniteComparisons.comparison1195
#print axioms sourceMap1195_checked
#print axioms fusedMap1195_checked
#print axioms certified1195
def sourceMap1195swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![2,1,0,8,9,10,11,12,13,6,3,4,5,7] (sourceLabel 9 2 0 v)
def fusedMap1195swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1195swap_checked : acceptsGraphIso
    (source (graph core1195) (root 9) 2 0) DegreeTwoThreeSpectrum1885.graph sourceMap1195swap=true := by decide +kernel
theorem fusedMap1195swap_checked : acceptsGraphIso
    (fused (graph core1195) (root 9) 2 0) DegreeTwoThreeSpectrum1727.graph fusedMap1195swap=true := by decide +kernel
theorem certified1195swap : Certified (graph core1195) (root 9) 2 0 :=
  of_native_maps core1195 DegreeTwoThreeSpectrum1885.graph DegreeTwoThreeSpectrum1727.graph
    sourceMap1195swap fusedMap1195swap sourceMap1195swap_checked fusedMap1195swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1195
#print axioms sourceMap1195swap_checked
#print axioms fusedMap1195swap_checked
#print axioms certified1195swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
