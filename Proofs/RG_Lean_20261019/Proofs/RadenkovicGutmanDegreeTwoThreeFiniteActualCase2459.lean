/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2459 : Family 10 := level10.get ⟨43,by decide⟩
def sourceMap2459 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,7,8,2,3,4,5,6] (sourceLabel 10 0 4 v)
def fusedMap2459 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2459_checked : acceptsGraphIso
    (source (graph core2459) (root 10) 0 4) DegreeTwoThreeSpectrum5113.graph sourceMap2459=true := by decide +kernel
theorem fusedMap2459_checked : acceptsGraphIso
    (fused (graph core2459) (root 10) 0 4) DegreeTwoThreeSpectrum5122.graph fusedMap2459=true := by decide +kernel
theorem certified2459 : Certified (graph core2459) (root 10) 0 4 :=
  of_native_maps core2459 DegreeTwoThreeSpectrum5113.graph DegreeTwoThreeSpectrum5122.graph
    sourceMap2459 fusedMap2459 sourceMap2459_checked fusedMap2459_checked
    DegreeTwoThreeFiniteComparisons.comparison2459
#print axioms sourceMap2459_checked
#print axioms fusedMap2459_checked
#print axioms certified2459
def sourceMap2459swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,7,2,3,4,5,6,8] (sourceLabel 10 4 0 v)
def fusedMap2459swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2459swap_checked : acceptsGraphIso
    (source (graph core2459) (root 10) 4 0) DegreeTwoThreeSpectrum5113.graph sourceMap2459swap=true := by decide +kernel
theorem fusedMap2459swap_checked : acceptsGraphIso
    (fused (graph core2459) (root 10) 4 0) DegreeTwoThreeSpectrum5122.graph fusedMap2459swap=true := by decide +kernel
theorem certified2459swap : Certified (graph core2459) (root 10) 4 0 :=
  of_native_maps core2459 DegreeTwoThreeSpectrum5113.graph DegreeTwoThreeSpectrum5122.graph
    sourceMap2459swap fusedMap2459swap sourceMap2459swap_checked fusedMap2459swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2459
#print axioms sourceMap2459swap_checked
#print axioms fusedMap2459swap_checked
#print axioms certified2459swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
