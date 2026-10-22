/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2124 : Family 8 := level8.get ⟨31,by decide⟩
def sourceMap2124 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,6,7,1,2,3,4,5] (sourceLabel 8 0 4 v)
def fusedMap2124 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (fusedLabel 8 0 4 v)
theorem sourceMap2124_checked : acceptsGraphIso
    (source (graph core2124) (root 8) 0 4) DegreeTwoThreeSpectrum2432.graph sourceMap2124=true := by decide +kernel
theorem fusedMap2124_checked : acceptsGraphIso
    (fused (graph core2124) (root 8) 0 4) DegreeTwoThreeSpectrum2434.graph fusedMap2124=true := by decide +kernel
theorem certified2124 : Certified (graph core2124) (root 8) 0 4 :=
  of_native_maps core2124 DegreeTwoThreeSpectrum2432.graph DegreeTwoThreeSpectrum2434.graph
    sourceMap2124 fusedMap2124 sourceMap2124_checked fusedMap2124_checked
    DegreeTwoThreeFiniteComparisons.comparison2124
#print axioms sourceMap2124_checked
#print axioms fusedMap2124_checked
#print axioms certified2124
def sourceMap2124swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,6,1,2,3,4,5,7] (sourceLabel 8 4 0 v)
def fusedMap2124swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (fusedLabel 8 4 0 v)
theorem sourceMap2124swap_checked : acceptsGraphIso
    (source (graph core2124) (root 8) 4 0) DegreeTwoThreeSpectrum2432.graph sourceMap2124swap=true := by decide +kernel
theorem fusedMap2124swap_checked : acceptsGraphIso
    (fused (graph core2124) (root 8) 4 0) DegreeTwoThreeSpectrum2434.graph fusedMap2124swap=true := by decide +kernel
theorem certified2124swap : Certified (graph core2124) (root 8) 4 0 :=
  of_native_maps core2124 DegreeTwoThreeSpectrum2432.graph DegreeTwoThreeSpectrum2434.graph
    sourceMap2124swap fusedMap2124swap sourceMap2124swap_checked fusedMap2124swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2124
#print axioms sourceMap2124swap_checked
#print axioms fusedMap2124swap_checked
#print axioms certified2124swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
