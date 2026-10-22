/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2147 : Family 8 := level8.get ⟨105,by decide⟩
def sourceMap2147 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2147 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2147_checked : acceptsGraphIso
    (source (graph core2147) (root 8) 0 4) DegreeTwoThreeSpectrum2480.graph sourceMap2147=true := by decide +kernel
theorem fusedMap2147_checked : acceptsGraphIso
    (fused (graph core2147) (root 8) 0 4) DegreeTwoThreeSpectrum2482.graph fusedMap2147=true := by decide +kernel
theorem certified2147 : Certified (graph core2147) (root 8) 0 4 :=
  of_native_maps core2147 DegreeTwoThreeSpectrum2480.graph DegreeTwoThreeSpectrum2482.graph
    sourceMap2147 fusedMap2147 sourceMap2147_checked fusedMap2147_checked
    DegreeTwoThreeFiniteComparisons.comparison2147
#print axioms sourceMap2147_checked
#print axioms fusedMap2147_checked
#print axioms certified2147
def sourceMap2147swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2147swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2147swap_checked : acceptsGraphIso
    (source (graph core2147) (root 8) 4 0) DegreeTwoThreeSpectrum2480.graph sourceMap2147swap=true := by decide +kernel
theorem fusedMap2147swap_checked : acceptsGraphIso
    (fused (graph core2147) (root 8) 4 0) DegreeTwoThreeSpectrum2482.graph fusedMap2147swap=true := by decide +kernel
theorem certified2147swap : Certified (graph core2147) (root 8) 4 0 :=
  of_native_maps core2147 DegreeTwoThreeSpectrum2480.graph DegreeTwoThreeSpectrum2482.graph
    sourceMap2147swap fusedMap2147swap sourceMap2147swap_checked fusedMap2147swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2147
#print axioms sourceMap2147swap_checked
#print axioms fusedMap2147swap_checked
#print axioms certified2147swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
