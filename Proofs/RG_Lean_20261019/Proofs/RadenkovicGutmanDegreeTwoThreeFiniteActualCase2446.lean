/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2446 : Family 9 := level9.get ⟨657,by decide⟩
def sourceMap2446 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2446 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2446_checked : acceptsGraphIso
    (source (graph core2446) (root 9) 0 4) DegreeTwoThreeSpectrum4823.graph sourceMap2446=true := by decide +kernel
theorem fusedMap2446_checked : acceptsGraphIso
    (fused (graph core2446) (root 9) 0 4) DegreeTwoThreeSpectrum4456.graph fusedMap2446=true := by decide +kernel
theorem certified2446 : Certified (graph core2446) (root 9) 0 4 :=
  of_native_maps core2446 DegreeTwoThreeSpectrum4823.graph DegreeTwoThreeSpectrum4456.graph
    sourceMap2446 fusedMap2446 sourceMap2446_checked fusedMap2446_checked
    DegreeTwoThreeFiniteComparisons.comparison2446
#print axioms sourceMap2446_checked
#print axioms fusedMap2446_checked
#print axioms certified2446
def sourceMap2446swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2446swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2446swap_checked : acceptsGraphIso
    (source (graph core2446) (root 9) 4 0) DegreeTwoThreeSpectrum4823.graph sourceMap2446swap=true := by decide +kernel
theorem fusedMap2446swap_checked : acceptsGraphIso
    (fused (graph core2446) (root 9) 4 0) DegreeTwoThreeSpectrum4456.graph fusedMap2446swap=true := by decide +kernel
theorem certified2446swap : Certified (graph core2446) (root 9) 4 0 :=
  of_native_maps core2446 DegreeTwoThreeSpectrum4823.graph DegreeTwoThreeSpectrum4456.graph
    sourceMap2446swap fusedMap2446swap sourceMap2446swap_checked fusedMap2446swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2446
#print axioms sourceMap2446swap_checked
#print axioms fusedMap2446swap_checked
#print axioms certified2446swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
