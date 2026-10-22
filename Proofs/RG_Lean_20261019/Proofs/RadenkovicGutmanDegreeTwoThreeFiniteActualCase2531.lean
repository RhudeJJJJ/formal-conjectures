/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2531 : Family 10 := level10.get ⟨320,by decide⟩
def sourceMap2531 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2531 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2531_checked : acceptsGraphIso
    (source (graph core2531) (root 10) 0 4) DegreeTwoThreeSpectrum5534.graph sourceMap2531=true := by decide +kernel
theorem fusedMap2531_checked : acceptsGraphIso
    (fused (graph core2531) (root 10) 0 4) DegreeTwoThreeSpectrum5535.graph fusedMap2531=true := by decide +kernel
theorem certified2531 : Certified (graph core2531) (root 10) 0 4 :=
  of_native_maps core2531 DegreeTwoThreeSpectrum5534.graph DegreeTwoThreeSpectrum5535.graph
    sourceMap2531 fusedMap2531 sourceMap2531_checked fusedMap2531_checked
    DegreeTwoThreeFiniteComparisons.comparison2531
#print axioms sourceMap2531_checked
#print axioms fusedMap2531_checked
#print axioms certified2531
def sourceMap2531swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2531swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2531swap_checked : acceptsGraphIso
    (source (graph core2531) (root 10) 4 0) DegreeTwoThreeSpectrum5534.graph sourceMap2531swap=true := by decide +kernel
theorem fusedMap2531swap_checked : acceptsGraphIso
    (fused (graph core2531) (root 10) 4 0) DegreeTwoThreeSpectrum5535.graph fusedMap2531swap=true := by decide +kernel
theorem certified2531swap : Certified (graph core2531) (root 10) 4 0 :=
  of_native_maps core2531 DegreeTwoThreeSpectrum5534.graph DegreeTwoThreeSpectrum5535.graph
    sourceMap2531swap fusedMap2531swap sourceMap2531swap_checked fusedMap2531swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2531
#print axioms sourceMap2531swap_checked
#print axioms fusedMap2531swap_checked
#print axioms certified2531swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
