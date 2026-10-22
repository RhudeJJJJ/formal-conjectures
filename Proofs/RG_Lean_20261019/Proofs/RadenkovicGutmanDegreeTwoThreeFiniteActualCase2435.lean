/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2435 : Family 9 := level9.get ⟨632,by decide⟩
def sourceMap2435 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2435 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2435_checked : acceptsGraphIso
    (source (graph core2435) (root 9) 0 4) DegreeTwoThreeSpectrum4790.graph sourceMap2435=true := by decide +kernel
theorem fusedMap2435_checked : acceptsGraphIso
    (fused (graph core2435) (root 9) 0 4) DegreeTwoThreeSpectrum4392.graph fusedMap2435=true := by decide +kernel
theorem certified2435 : Certified (graph core2435) (root 9) 0 4 :=
  of_native_maps core2435 DegreeTwoThreeSpectrum4790.graph DegreeTwoThreeSpectrum4392.graph
    sourceMap2435 fusedMap2435 sourceMap2435_checked fusedMap2435_checked
    DegreeTwoThreeFiniteComparisons.comparison2435
#print axioms sourceMap2435_checked
#print axioms fusedMap2435_checked
#print axioms certified2435
def sourceMap2435swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2435swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2435swap_checked : acceptsGraphIso
    (source (graph core2435) (root 9) 4 0) DegreeTwoThreeSpectrum4790.graph sourceMap2435swap=true := by decide +kernel
theorem fusedMap2435swap_checked : acceptsGraphIso
    (fused (graph core2435) (root 9) 4 0) DegreeTwoThreeSpectrum4392.graph fusedMap2435swap=true := by decide +kernel
theorem certified2435swap : Certified (graph core2435) (root 9) 4 0 :=
  of_native_maps core2435 DegreeTwoThreeSpectrum4790.graph DegreeTwoThreeSpectrum4392.graph
    sourceMap2435swap fusedMap2435swap sourceMap2435swap_checked fusedMap2435swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2435
#print axioms sourceMap2435swap_checked
#print axioms fusedMap2435swap_checked
#print axioms certified2435swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
