/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2519 : Family 10 := level10.get ⟨277,by decide⟩
def sourceMap2519 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2519 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2519_checked : acceptsGraphIso
    (source (graph core2519) (root 10) 0 4) DegreeTwoThreeSpectrum5407.graph sourceMap2519=true := by decide +kernel
theorem fusedMap2519_checked : acceptsGraphIso
    (fused (graph core2519) (root 10) 0 4) DegreeTwoThreeSpectrum5408.graph fusedMap2519=true := by decide +kernel
theorem certified2519 : Certified (graph core2519) (root 10) 0 4 :=
  of_native_maps core2519 DegreeTwoThreeSpectrum5407.graph DegreeTwoThreeSpectrum5408.graph
    sourceMap2519 fusedMap2519 sourceMap2519_checked fusedMap2519_checked
    DegreeTwoThreeFiniteComparisons.comparison2519
#print axioms sourceMap2519_checked
#print axioms fusedMap2519_checked
#print axioms certified2519
def sourceMap2519swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2519swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2519swap_checked : acceptsGraphIso
    (source (graph core2519) (root 10) 4 0) DegreeTwoThreeSpectrum5407.graph sourceMap2519swap=true := by decide +kernel
theorem fusedMap2519swap_checked : acceptsGraphIso
    (fused (graph core2519) (root 10) 4 0) DegreeTwoThreeSpectrum5408.graph fusedMap2519swap=true := by decide +kernel
theorem certified2519swap : Certified (graph core2519) (root 10) 4 0 :=
  of_native_maps core2519 DegreeTwoThreeSpectrum5407.graph DegreeTwoThreeSpectrum5408.graph
    sourceMap2519swap fusedMap2519swap sourceMap2519swap_checked fusedMap2519swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2519
#print axioms sourceMap2519swap_checked
#print axioms fusedMap2519swap_checked
#print axioms certified2519swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
