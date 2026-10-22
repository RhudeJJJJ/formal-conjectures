/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2995 : Family 10 := level10.get ⟨1555,by decide⟩
def sourceMap2995 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2995 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2995_checked : acceptsGraphIso
    (source (graph core2995) (root 10) 0 4) DegreeTwoThreeSpectrum7092.graph sourceMap2995=true := by decide +kernel
theorem fusedMap2995_checked : acceptsGraphIso
    (fused (graph core2995) (root 10) 0 4) DegreeTwoThreeSpectrum6011.graph fusedMap2995=true := by decide +kernel
theorem certified2995 : Certified (graph core2995) (root 10) 0 4 :=
  of_native_maps core2995 DegreeTwoThreeSpectrum7092.graph DegreeTwoThreeSpectrum6011.graph
    sourceMap2995 fusedMap2995 sourceMap2995_checked fusedMap2995_checked
    DegreeTwoThreeFiniteComparisons.comparison2995
#print axioms sourceMap2995_checked
#print axioms fusedMap2995_checked
#print axioms certified2995
def sourceMap2995swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap2995swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2995swap_checked : acceptsGraphIso
    (source (graph core2995) (root 10) 4 0) DegreeTwoThreeSpectrum7092.graph sourceMap2995swap=true := by decide +kernel
theorem fusedMap2995swap_checked : acceptsGraphIso
    (fused (graph core2995) (root 10) 4 0) DegreeTwoThreeSpectrum6011.graph fusedMap2995swap=true := by decide +kernel
theorem certified2995swap : Certified (graph core2995) (root 10) 4 0 :=
  of_native_maps core2995 DegreeTwoThreeSpectrum7092.graph DegreeTwoThreeSpectrum6011.graph
    sourceMap2995swap fusedMap2995swap sourceMap2995swap_checked fusedMap2995swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2995
#print axioms sourceMap2995swap_checked
#print axioms fusedMap2995swap_checked
#print axioms certified2995swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
