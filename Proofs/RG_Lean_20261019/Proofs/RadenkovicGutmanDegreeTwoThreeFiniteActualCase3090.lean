/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3090 : Family 6 := level6.get ⟨16,by decide⟩
def sourceMap3090 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (sourceLabel 6 0 5 v)
def fusedMap3090 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13] (fusedLabel 6 0 5 v)
theorem sourceMap3090_checked : acceptsGraphIso
    (source (graph core3090) (root 6) 0 5) DegreeTwoThreeSpectrum1894.graph sourceMap3090=true := by decide +kernel
theorem fusedMap3090_checked : acceptsGraphIso
    (fused (graph core3090) (root 6) 0 5) DegreeTwoThreeSpectrum1725.graph fusedMap3090=true := by decide +kernel
theorem certified3090 : Certified (graph core3090) (root 6) 0 5 :=
  of_native_maps core3090 DegreeTwoThreeSpectrum1894.graph DegreeTwoThreeSpectrum1725.graph
    sourceMap3090 fusedMap3090 sourceMap3090_checked fusedMap3090_checked
    DegreeTwoThreeFiniteComparisons.comparison3090
#print axioms sourceMap3090_checked
#print axioms fusedMap3090_checked
#print axioms certified3090
def sourceMap3090swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,13,8] (sourceLabel 6 5 0 v)
def fusedMap3090swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13] (fusedLabel 6 5 0 v)
theorem sourceMap3090swap_checked : acceptsGraphIso
    (source (graph core3090) (root 6) 5 0) DegreeTwoThreeSpectrum1894.graph sourceMap3090swap=true := by decide +kernel
theorem fusedMap3090swap_checked : acceptsGraphIso
    (fused (graph core3090) (root 6) 5 0) DegreeTwoThreeSpectrum1725.graph fusedMap3090swap=true := by decide +kernel
theorem certified3090swap : Certified (graph core3090) (root 6) 5 0 :=
  of_native_maps core3090 DegreeTwoThreeSpectrum1894.graph DegreeTwoThreeSpectrum1725.graph
    sourceMap3090swap fusedMap3090swap sourceMap3090swap_checked fusedMap3090swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3090
#print axioms sourceMap3090swap_checked
#print axioms fusedMap3090swap_checked
#print axioms certified3090swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
