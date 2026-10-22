/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2209 : Family 8 := level8.get ⟨250,by decide⟩
def sourceMap2209 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2209 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2209_checked : acceptsGraphIso
    (source (graph core2209) (root 8) 0 4) DegreeTwoThreeSpectrum3543.graph sourceMap2209=true := by decide +kernel
theorem fusedMap2209_checked : acceptsGraphIso
    (fused (graph core2209) (root 8) 0 4) DegreeTwoThreeSpectrum2735.graph fusedMap2209=true := by decide +kernel
theorem certified2209 : Certified (graph core2209) (root 8) 0 4 :=
  of_native_maps core2209 DegreeTwoThreeSpectrum3543.graph DegreeTwoThreeSpectrum2735.graph
    sourceMap2209 fusedMap2209 sourceMap2209_checked fusedMap2209_checked
    DegreeTwoThreeFiniteComparisons.comparison2209
#print axioms sourceMap2209_checked
#print axioms fusedMap2209_checked
#print axioms certified2209
def sourceMap2209swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2209swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2209swap_checked : acceptsGraphIso
    (source (graph core2209) (root 8) 4 0) DegreeTwoThreeSpectrum3543.graph sourceMap2209swap=true := by decide +kernel
theorem fusedMap2209swap_checked : acceptsGraphIso
    (fused (graph core2209) (root 8) 4 0) DegreeTwoThreeSpectrum2735.graph fusedMap2209swap=true := by decide +kernel
theorem certified2209swap : Certified (graph core2209) (root 8) 4 0 :=
  of_native_maps core2209 DegreeTwoThreeSpectrum3543.graph DegreeTwoThreeSpectrum2735.graph
    sourceMap2209swap fusedMap2209swap sourceMap2209swap_checked fusedMap2209swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2209
#print axioms sourceMap2209swap_checked
#print axioms fusedMap2209swap_checked
#print axioms certified2209swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
