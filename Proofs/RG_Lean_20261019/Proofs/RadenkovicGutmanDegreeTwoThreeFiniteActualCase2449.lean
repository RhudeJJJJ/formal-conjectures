/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2449 : Family 9 := level9.get ⟨678,by decide⟩
def sourceMap2449 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2449 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2449_checked : acceptsGraphIso
    (source (graph core2449) (root 9) 0 4) DegreeTwoThreeSpectrum4900.graph sourceMap2449=true := by decide +kernel
theorem fusedMap2449_checked : acceptsGraphIso
    (fused (graph core2449) (root 9) 0 4) DegreeTwoThreeSpectrum4562.graph fusedMap2449=true := by decide +kernel
theorem certified2449 : Certified (graph core2449) (root 9) 0 4 :=
  of_native_maps core2449 DegreeTwoThreeSpectrum4900.graph DegreeTwoThreeSpectrum4562.graph
    sourceMap2449 fusedMap2449 sourceMap2449_checked fusedMap2449_checked
    DegreeTwoThreeFiniteComparisons.comparison2449
#print axioms sourceMap2449_checked
#print axioms fusedMap2449_checked
#print axioms certified2449
def sourceMap2449swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2449swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2449swap_checked : acceptsGraphIso
    (source (graph core2449) (root 9) 4 0) DegreeTwoThreeSpectrum4900.graph sourceMap2449swap=true := by decide +kernel
theorem fusedMap2449swap_checked : acceptsGraphIso
    (fused (graph core2449) (root 9) 4 0) DegreeTwoThreeSpectrum4562.graph fusedMap2449swap=true := by decide +kernel
theorem certified2449swap : Certified (graph core2449) (root 9) 4 0 :=
  of_native_maps core2449 DegreeTwoThreeSpectrum4900.graph DegreeTwoThreeSpectrum4562.graph
    sourceMap2449swap fusedMap2449swap sourceMap2449swap_checked fusedMap2449swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2449
#print axioms sourceMap2449swap_checked
#print axioms fusedMap2449swap_checked
#print axioms certified2449swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
