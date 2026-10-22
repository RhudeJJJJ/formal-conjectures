/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2208 : Family 8 := level8.get ⟨248,by decide⟩
def sourceMap2208 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2208 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2208_checked : acceptsGraphIso
    (source (graph core2208) (root 8) 0 4) DegreeTwoThreeSpectrum3528.graph sourceMap2208=true := by decide +kernel
theorem fusedMap2208_checked : acceptsGraphIso
    (fused (graph core2208) (root 8) 0 4) DegreeTwoThreeSpectrum2731.graph fusedMap2208=true := by decide +kernel
theorem certified2208 : Certified (graph core2208) (root 8) 0 4 :=
  of_native_maps core2208 DegreeTwoThreeSpectrum3528.graph DegreeTwoThreeSpectrum2731.graph
    sourceMap2208 fusedMap2208 sourceMap2208_checked fusedMap2208_checked
    DegreeTwoThreeFiniteComparisons.comparison2208
#print axioms sourceMap2208_checked
#print axioms fusedMap2208_checked
#print axioms certified2208
def sourceMap2208swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2208swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2208swap_checked : acceptsGraphIso
    (source (graph core2208) (root 8) 4 0) DegreeTwoThreeSpectrum3528.graph sourceMap2208swap=true := by decide +kernel
theorem fusedMap2208swap_checked : acceptsGraphIso
    (fused (graph core2208) (root 8) 4 0) DegreeTwoThreeSpectrum2731.graph fusedMap2208swap=true := by decide +kernel
theorem certified2208swap : Certified (graph core2208) (root 8) 4 0 :=
  of_native_maps core2208 DegreeTwoThreeSpectrum3528.graph DegreeTwoThreeSpectrum2731.graph
    sourceMap2208swap fusedMap2208swap sourceMap2208swap_checked fusedMap2208swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2208
#print axioms sourceMap2208swap_checked
#print axioms fusedMap2208swap_checked
#print axioms certified2208swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
