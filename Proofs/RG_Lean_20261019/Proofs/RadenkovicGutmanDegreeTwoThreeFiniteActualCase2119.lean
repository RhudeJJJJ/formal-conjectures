/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2119 : Family 8 := level8.get ⟨7,by decide⟩
def sourceMap2119 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,7,8,2,3,4,5,6] (sourceLabel 8 0 4 v)
def fusedMap2119 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,7,1,2,3,4,5,6] (fusedLabel 8 0 4 v)
theorem sourceMap2119_checked : acceptsGraphIso
    (source (graph core2119) (root 8) 0 4) DegreeTwoThreeSpectrum2433.graph sourceMap2119=true := by decide +kernel
theorem fusedMap2119_checked : acceptsGraphIso
    (fused (graph core2119) (root 8) 0 4) DegreeTwoThreeSpectrum2314.graph fusedMap2119=true := by decide +kernel
theorem certified2119 : Certified (graph core2119) (root 8) 0 4 :=
  of_native_maps core2119 DegreeTwoThreeSpectrum2433.graph DegreeTwoThreeSpectrum2314.graph
    sourceMap2119 fusedMap2119 sourceMap2119_checked fusedMap2119_checked
    DegreeTwoThreeFiniteComparisons.comparison2119
#print axioms sourceMap2119_checked
#print axioms fusedMap2119_checked
#print axioms certified2119
def sourceMap2119swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,7,2,3,4,5,6,8] (sourceLabel 8 4 0 v)
def fusedMap2119swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,7,1,2,3,4,5,6] (fusedLabel 8 4 0 v)
theorem sourceMap2119swap_checked : acceptsGraphIso
    (source (graph core2119) (root 8) 4 0) DegreeTwoThreeSpectrum2433.graph sourceMap2119swap=true := by decide +kernel
theorem fusedMap2119swap_checked : acceptsGraphIso
    (fused (graph core2119) (root 8) 4 0) DegreeTwoThreeSpectrum2314.graph fusedMap2119swap=true := by decide +kernel
theorem certified2119swap : Certified (graph core2119) (root 8) 4 0 :=
  of_native_maps core2119 DegreeTwoThreeSpectrum2433.graph DegreeTwoThreeSpectrum2314.graph
    sourceMap2119swap fusedMap2119swap sourceMap2119swap_checked fusedMap2119swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2119
#print axioms sourceMap2119swap_checked
#print axioms fusedMap2119swap_checked
#print axioms certified2119swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
