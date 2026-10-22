/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2194 : Family 8 := level8.get ⟨218,by decide⟩
def sourceMap2194 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2194 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2194_checked : acceptsGraphIso
    (source (graph core2194) (root 8) 0 4) DegreeTwoThreeSpectrum3241.graph sourceMap2194=true := by decide +kernel
theorem fusedMap2194_checked : acceptsGraphIso
    (fused (graph core2194) (root 8) 0 4) DegreeTwoThreeSpectrum2532.graph fusedMap2194=true := by decide +kernel
theorem certified2194 : Certified (graph core2194) (root 8) 0 4 :=
  of_native_maps core2194 DegreeTwoThreeSpectrum3241.graph DegreeTwoThreeSpectrum2532.graph
    sourceMap2194 fusedMap2194 sourceMap2194_checked fusedMap2194_checked
    DegreeTwoThreeFiniteComparisons.comparison2194
#print axioms sourceMap2194_checked
#print axioms fusedMap2194_checked
#print axioms certified2194
def sourceMap2194swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2194swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2194swap_checked : acceptsGraphIso
    (source (graph core2194) (root 8) 4 0) DegreeTwoThreeSpectrum3241.graph sourceMap2194swap=true := by decide +kernel
theorem fusedMap2194swap_checked : acceptsGraphIso
    (fused (graph core2194) (root 8) 4 0) DegreeTwoThreeSpectrum2532.graph fusedMap2194swap=true := by decide +kernel
theorem certified2194swap : Certified (graph core2194) (root 8) 4 0 :=
  of_native_maps core2194 DegreeTwoThreeSpectrum3241.graph DegreeTwoThreeSpectrum2532.graph
    sourceMap2194swap fusedMap2194swap sourceMap2194swap_checked fusedMap2194swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2194
#print axioms sourceMap2194swap_checked
#print axioms fusedMap2194swap_checked
#print axioms certified2194swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
