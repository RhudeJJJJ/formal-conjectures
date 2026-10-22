/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2318 : Family 9 := level9.get ⟨345,by decide⟩
def sourceMap2318 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2318 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2318_checked : acceptsGraphIso
    (source (graph core2318) (root 9) 0 4) DegreeTwoThreeSpectrum4242.graph sourceMap2318=true := by decide +kernel
theorem fusedMap2318_checked : acceptsGraphIso
    (fused (graph core2318) (root 9) 0 4) DegreeTwoThreeSpectrum4243.graph fusedMap2318=true := by decide +kernel
theorem certified2318 : Certified (graph core2318) (root 9) 0 4 :=
  of_native_maps core2318 DegreeTwoThreeSpectrum4242.graph DegreeTwoThreeSpectrum4243.graph
    sourceMap2318 fusedMap2318 sourceMap2318_checked fusedMap2318_checked
    DegreeTwoThreeFiniteComparisons.comparison2318
#print axioms sourceMap2318_checked
#print axioms fusedMap2318_checked
#print axioms certified2318
def sourceMap2318swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2318swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2318swap_checked : acceptsGraphIso
    (source (graph core2318) (root 9) 4 0) DegreeTwoThreeSpectrum4242.graph sourceMap2318swap=true := by decide +kernel
theorem fusedMap2318swap_checked : acceptsGraphIso
    (fused (graph core2318) (root 9) 4 0) DegreeTwoThreeSpectrum4243.graph fusedMap2318swap=true := by decide +kernel
theorem certified2318swap : Certified (graph core2318) (root 9) 4 0 :=
  of_native_maps core2318 DegreeTwoThreeSpectrum4242.graph DegreeTwoThreeSpectrum4243.graph
    sourceMap2318swap fusedMap2318swap sourceMap2318swap_checked fusedMap2318swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2318
#print axioms sourceMap2318swap_checked
#print axioms fusedMap2318swap_checked
#print axioms certified2318swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
