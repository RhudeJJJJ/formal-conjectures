/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2317 : Family 9 := level9.get ⟨340,by decide⟩
def sourceMap2317 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2317 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2317_checked : acceptsGraphIso
    (source (graph core2317) (root 9) 0 4) DegreeTwoThreeSpectrum4229.graph sourceMap2317=true := by decide +kernel
theorem fusedMap2317_checked : acceptsGraphIso
    (fused (graph core2317) (root 9) 0 4) DegreeTwoThreeSpectrum4230.graph fusedMap2317=true := by decide +kernel
theorem certified2317 : Certified (graph core2317) (root 9) 0 4 :=
  of_native_maps core2317 DegreeTwoThreeSpectrum4229.graph DegreeTwoThreeSpectrum4230.graph
    sourceMap2317 fusedMap2317 sourceMap2317_checked fusedMap2317_checked
    DegreeTwoThreeFiniteComparisons.comparison2317
#print axioms sourceMap2317_checked
#print axioms fusedMap2317_checked
#print axioms certified2317
def sourceMap2317swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2317swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2317swap_checked : acceptsGraphIso
    (source (graph core2317) (root 9) 4 0) DegreeTwoThreeSpectrum4229.graph sourceMap2317swap=true := by decide +kernel
theorem fusedMap2317swap_checked : acceptsGraphIso
    (fused (graph core2317) (root 9) 4 0) DegreeTwoThreeSpectrum4230.graph fusedMap2317swap=true := by decide +kernel
theorem certified2317swap : Certified (graph core2317) (root 9) 4 0 :=
  of_native_maps core2317 DegreeTwoThreeSpectrum4229.graph DegreeTwoThreeSpectrum4230.graph
    sourceMap2317swap fusedMap2317swap sourceMap2317swap_checked fusedMap2317swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2317
#print axioms sourceMap2317swap_checked
#print axioms fusedMap2317swap_checked
#print axioms certified2317swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
