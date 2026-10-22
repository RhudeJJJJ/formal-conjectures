/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3091 : Family 6 := level6.get ⟨17,by decide⟩
def sourceMap3091 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (sourceLabel 6 0 5 v)
def fusedMap3091 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13] (fusedLabel 6 0 5 v)
theorem sourceMap3091_checked : acceptsGraphIso
    (source (graph core3091) (root 6) 0 5) DegreeTwoThreeSpectrum1914.graph sourceMap3091=true := by decide +kernel
theorem fusedMap3091_checked : acceptsGraphIso
    (fused (graph core3091) (root 6) 0 5) DegreeTwoThreeSpectrum1729.graph fusedMap3091=true := by decide +kernel
theorem certified3091 : Certified (graph core3091) (root 6) 0 5 :=
  of_native_maps core3091 DegreeTwoThreeSpectrum1914.graph DegreeTwoThreeSpectrum1729.graph
    sourceMap3091 fusedMap3091 sourceMap3091_checked fusedMap3091_checked
    DegreeTwoThreeFiniteComparisons.comparison3091
#print axioms sourceMap3091_checked
#print axioms fusedMap3091_checked
#print axioms certified3091
def sourceMap3091swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,13,8] (sourceLabel 6 5 0 v)
def fusedMap3091swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13] (fusedLabel 6 5 0 v)
theorem sourceMap3091swap_checked : acceptsGraphIso
    (source (graph core3091) (root 6) 5 0) DegreeTwoThreeSpectrum1914.graph sourceMap3091swap=true := by decide +kernel
theorem fusedMap3091swap_checked : acceptsGraphIso
    (fused (graph core3091) (root 6) 5 0) DegreeTwoThreeSpectrum1729.graph fusedMap3091swap=true := by decide +kernel
theorem certified3091swap : Certified (graph core3091) (root 6) 5 0 :=
  of_native_maps core3091 DegreeTwoThreeSpectrum1914.graph DegreeTwoThreeSpectrum1729.graph
    sourceMap3091swap fusedMap3091swap sourceMap3091swap_checked fusedMap3091swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3091
#print axioms sourceMap3091swap_checked
#print axioms fusedMap3091swap_checked
#print axioms certified3091swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
