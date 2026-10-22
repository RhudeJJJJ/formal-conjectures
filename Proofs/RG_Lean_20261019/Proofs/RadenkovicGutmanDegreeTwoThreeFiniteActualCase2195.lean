/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2195 : Family 8 := level8.get ⟨219,by decide⟩
def sourceMap2195 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2195 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2195_checked : acceptsGraphIso
    (source (graph core2195) (root 8) 0 4) DegreeTwoThreeSpectrum3245.graph sourceMap2195=true := by decide +kernel
theorem fusedMap2195_checked : acceptsGraphIso
    (fused (graph core2195) (root 8) 0 4) DegreeTwoThreeSpectrum2533.graph fusedMap2195=true := by decide +kernel
theorem certified2195 : Certified (graph core2195) (root 8) 0 4 :=
  of_native_maps core2195 DegreeTwoThreeSpectrum3245.graph DegreeTwoThreeSpectrum2533.graph
    sourceMap2195 fusedMap2195 sourceMap2195_checked fusedMap2195_checked
    DegreeTwoThreeFiniteComparisons.comparison2195
#print axioms sourceMap2195_checked
#print axioms fusedMap2195_checked
#print axioms certified2195
def sourceMap2195swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2195swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2195swap_checked : acceptsGraphIso
    (source (graph core2195) (root 8) 4 0) DegreeTwoThreeSpectrum3245.graph sourceMap2195swap=true := by decide +kernel
theorem fusedMap2195swap_checked : acceptsGraphIso
    (fused (graph core2195) (root 8) 4 0) DegreeTwoThreeSpectrum2533.graph fusedMap2195swap=true := by decide +kernel
theorem certified2195swap : Certified (graph core2195) (root 8) 4 0 :=
  of_native_maps core2195 DegreeTwoThreeSpectrum3245.graph DegreeTwoThreeSpectrum2533.graph
    sourceMap2195swap fusedMap2195swap sourceMap2195swap_checked fusedMap2195swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2195
#print axioms sourceMap2195swap_checked
#print axioms fusedMap2195swap_checked
#print axioms certified2195swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
