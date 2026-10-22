/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2090 : Family 7 := level7.get ⟨36,by decide⟩
def sourceMap2090 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2090 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2090_checked : acceptsGraphIso
    (source (graph core2090) (root 7) 0 4) DegreeTwoThreeSpectrum1782.graph sourceMap2090=true := by decide +kernel
theorem fusedMap2090_checked : acceptsGraphIso
    (fused (graph core2090) (root 7) 0 4) DegreeTwoThreeSpectrum1784.graph fusedMap2090=true := by decide +kernel
theorem certified2090 : Certified (graph core2090) (root 7) 0 4 :=
  of_native_maps core2090 DegreeTwoThreeSpectrum1782.graph DegreeTwoThreeSpectrum1784.graph
    sourceMap2090 fusedMap2090 sourceMap2090_checked fusedMap2090_checked
    DegreeTwoThreeFiniteComparisons.comparison2090
#print axioms sourceMap2090_checked
#print axioms fusedMap2090_checked
#print axioms certified2090
def sourceMap2090swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,13,8] (sourceLabel 7 4 0 v)
def fusedMap2090swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2090swap_checked : acceptsGraphIso
    (source (graph core2090) (root 7) 4 0) DegreeTwoThreeSpectrum1782.graph sourceMap2090swap=true := by decide +kernel
theorem fusedMap2090swap_checked : acceptsGraphIso
    (fused (graph core2090) (root 7) 4 0) DegreeTwoThreeSpectrum1784.graph fusedMap2090swap=true := by decide +kernel
theorem certified2090swap : Certified (graph core2090) (root 7) 4 0 :=
  of_native_maps core2090 DegreeTwoThreeSpectrum1782.graph DegreeTwoThreeSpectrum1784.graph
    sourceMap2090swap fusedMap2090swap sourceMap2090swap_checked fusedMap2090swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2090
#print axioms sourceMap2090swap_checked
#print axioms fusedMap2090swap_checked
#print axioms certified2090swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
