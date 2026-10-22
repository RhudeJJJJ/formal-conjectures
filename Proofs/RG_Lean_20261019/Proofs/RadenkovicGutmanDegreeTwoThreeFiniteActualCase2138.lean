/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2138 : Family 8 := level8.get ⟨80,by decide⟩
def sourceMap2138 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12] (sourceLabel 8 0 4 v)
def fusedMap2138 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2138_checked : acceptsGraphIso
    (source (graph core2138) (root 8) 0 4) DegreeTwoThreeSpectrum2929.graph sourceMap2138=true := by decide +kernel
theorem fusedMap2138_checked : acceptsGraphIso
    (fused (graph core2138) (root 8) 0 4) DegreeTwoThreeSpectrum2396.graph fusedMap2138=true := by decide +kernel
theorem certified2138 : Certified (graph core2138) (root 8) 0 4 :=
  of_native_maps core2138 DegreeTwoThreeSpectrum2929.graph DegreeTwoThreeSpectrum2396.graph
    sourceMap2138 fusedMap2138 sourceMap2138_checked fusedMap2138_checked
    DegreeTwoThreeFiniteComparisons.comparison2138
#print axioms sourceMap2138_checked
#print axioms fusedMap2138_checked
#print axioms certified2138
def sourceMap2138swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,8,9,10,11,12,14] (sourceLabel 8 4 0 v)
def fusedMap2138swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2138swap_checked : acceptsGraphIso
    (source (graph core2138) (root 8) 4 0) DegreeTwoThreeSpectrum2929.graph sourceMap2138swap=true := by decide +kernel
theorem fusedMap2138swap_checked : acceptsGraphIso
    (fused (graph core2138) (root 8) 4 0) DegreeTwoThreeSpectrum2396.graph fusedMap2138swap=true := by decide +kernel
theorem certified2138swap : Certified (graph core2138) (root 8) 4 0 :=
  of_native_maps core2138 DegreeTwoThreeSpectrum2929.graph DegreeTwoThreeSpectrum2396.graph
    sourceMap2138swap fusedMap2138swap sourceMap2138swap_checked fusedMap2138swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2138
#print axioms sourceMap2138swap_checked
#print axioms fusedMap2138swap_checked
#print axioms certified2138swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
