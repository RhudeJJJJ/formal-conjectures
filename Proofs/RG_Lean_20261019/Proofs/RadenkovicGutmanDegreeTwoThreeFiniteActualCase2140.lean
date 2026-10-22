/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2140 : Family 8 := level8.get ⟨86,by decide⟩
def sourceMap2140 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12] (sourceLabel 8 0 4 v)
def fusedMap2140 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2140_checked : acceptsGraphIso
    (source (graph core2140) (root 8) 0 4) DegreeTwoThreeSpectrum2982.graph sourceMap2140=true := by decide +kernel
theorem fusedMap2140_checked : acceptsGraphIso
    (fused (graph core2140) (root 8) 0 4) DegreeTwoThreeSpectrum2411.graph fusedMap2140=true := by decide +kernel
theorem certified2140 : Certified (graph core2140) (root 8) 0 4 :=
  of_native_maps core2140 DegreeTwoThreeSpectrum2982.graph DegreeTwoThreeSpectrum2411.graph
    sourceMap2140 fusedMap2140 sourceMap2140_checked fusedMap2140_checked
    DegreeTwoThreeFiniteComparisons.comparison2140
#print axioms sourceMap2140_checked
#print axioms fusedMap2140_checked
#print axioms certified2140
def sourceMap2140swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,8,9,10,11,12,14] (sourceLabel 8 4 0 v)
def fusedMap2140swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2140swap_checked : acceptsGraphIso
    (source (graph core2140) (root 8) 4 0) DegreeTwoThreeSpectrum2982.graph sourceMap2140swap=true := by decide +kernel
theorem fusedMap2140swap_checked : acceptsGraphIso
    (fused (graph core2140) (root 8) 4 0) DegreeTwoThreeSpectrum2411.graph fusedMap2140swap=true := by decide +kernel
theorem certified2140swap : Certified (graph core2140) (root 8) 4 0 :=
  of_native_maps core2140 DegreeTwoThreeSpectrum2982.graph DegreeTwoThreeSpectrum2411.graph
    sourceMap2140swap fusedMap2140swap sourceMap2140swap_checked fusedMap2140swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2140
#print axioms sourceMap2140swap_checked
#print axioms fusedMap2140swap_checked
#print axioms certified2140swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
