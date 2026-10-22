/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2128 : Family 8 := level8.get ⟨47,by decide⟩
def sourceMap2128 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12] (sourceLabel 8 0 4 v)
def fusedMap2128 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2128_checked : acceptsGraphIso
    (source (graph core2128) (root 8) 0 4) DegreeTwoThreeSpectrum2601.graph sourceMap2128=true := by decide +kernel
theorem fusedMap2128_checked : acceptsGraphIso
    (fused (graph core2128) (root 8) 0 4) DegreeTwoThreeSpectrum2331.graph fusedMap2128=true := by decide +kernel
theorem certified2128 : Certified (graph core2128) (root 8) 0 4 :=
  of_native_maps core2128 DegreeTwoThreeSpectrum2601.graph DegreeTwoThreeSpectrum2331.graph
    sourceMap2128 fusedMap2128 sourceMap2128_checked fusedMap2128_checked
    DegreeTwoThreeFiniteComparisons.comparison2128
#print axioms sourceMap2128_checked
#print axioms fusedMap2128_checked
#print axioms certified2128
def sourceMap2128swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,8,9,10,11,12,14] (sourceLabel 8 4 0 v)
def fusedMap2128swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2128swap_checked : acceptsGraphIso
    (source (graph core2128) (root 8) 4 0) DegreeTwoThreeSpectrum2601.graph sourceMap2128swap=true := by decide +kernel
theorem fusedMap2128swap_checked : acceptsGraphIso
    (fused (graph core2128) (root 8) 4 0) DegreeTwoThreeSpectrum2331.graph fusedMap2128swap=true := by decide +kernel
theorem certified2128swap : Certified (graph core2128) (root 8) 4 0 :=
  of_native_maps core2128 DegreeTwoThreeSpectrum2601.graph DegreeTwoThreeSpectrum2331.graph
    sourceMap2128swap fusedMap2128swap sourceMap2128swap_checked fusedMap2128swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2128
#print axioms sourceMap2128swap_checked
#print axioms fusedMap2128swap_checked
#print axioms certified2128swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
