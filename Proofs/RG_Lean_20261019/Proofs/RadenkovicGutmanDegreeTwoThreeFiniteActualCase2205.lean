/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2205 : Family 8 := level8.get ⟨242,by decide⟩
def sourceMap2205 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2205 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2205_checked : acceptsGraphIso
    (source (graph core2205) (root 8) 0 4) DegreeTwoThreeSpectrum3474.graph sourceMap2205=true := by decide +kernel
theorem fusedMap2205_checked : acceptsGraphIso
    (fused (graph core2205) (root 8) 0 4) DegreeTwoThreeSpectrum2692.graph fusedMap2205=true := by decide +kernel
theorem certified2205 : Certified (graph core2205) (root 8) 0 4 :=
  of_native_maps core2205 DegreeTwoThreeSpectrum3474.graph DegreeTwoThreeSpectrum2692.graph
    sourceMap2205 fusedMap2205 sourceMap2205_checked fusedMap2205_checked
    DegreeTwoThreeFiniteComparisons.comparison2205
#print axioms sourceMap2205_checked
#print axioms fusedMap2205_checked
#print axioms certified2205
def sourceMap2205swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2205swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2205swap_checked : acceptsGraphIso
    (source (graph core2205) (root 8) 4 0) DegreeTwoThreeSpectrum3474.graph sourceMap2205swap=true := by decide +kernel
theorem fusedMap2205swap_checked : acceptsGraphIso
    (fused (graph core2205) (root 8) 4 0) DegreeTwoThreeSpectrum2692.graph fusedMap2205swap=true := by decide +kernel
theorem certified2205swap : Certified (graph core2205) (root 8) 4 0 :=
  of_native_maps core2205 DegreeTwoThreeSpectrum3474.graph DegreeTwoThreeSpectrum2692.graph
    sourceMap2205swap fusedMap2205swap sourceMap2205swap_checked fusedMap2205swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2205
#print axioms sourceMap2205swap_checked
#print axioms fusedMap2205swap_checked
#print axioms certified2205swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
