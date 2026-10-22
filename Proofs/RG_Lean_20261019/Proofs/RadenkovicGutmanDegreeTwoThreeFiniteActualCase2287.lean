/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2287 : Family 9 := level9.get ⟨261,by decide⟩
def sourceMap2287 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2287 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2287_checked : acceptsGraphIso
    (source (graph core2287) (root 9) 0 4) DegreeTwoThreeSpectrum4584.graph sourceMap2287=true := by decide +kernel
theorem fusedMap2287_checked : acceptsGraphIso
    (fused (graph core2287) (root 9) 0 4) DegreeTwoThreeSpectrum4070.graph fusedMap2287=true := by decide +kernel
theorem certified2287 : Certified (graph core2287) (root 9) 0 4 :=
  of_native_maps core2287 DegreeTwoThreeSpectrum4584.graph DegreeTwoThreeSpectrum4070.graph
    sourceMap2287 fusedMap2287 sourceMap2287_checked fusedMap2287_checked
    DegreeTwoThreeFiniteComparisons.comparison2287
#print axioms sourceMap2287_checked
#print axioms fusedMap2287_checked
#print axioms certified2287
def sourceMap2287swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2287swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2287swap_checked : acceptsGraphIso
    (source (graph core2287) (root 9) 4 0) DegreeTwoThreeSpectrum4584.graph sourceMap2287swap=true := by decide +kernel
theorem fusedMap2287swap_checked : acceptsGraphIso
    (fused (graph core2287) (root 9) 4 0) DegreeTwoThreeSpectrum4070.graph fusedMap2287swap=true := by decide +kernel
theorem certified2287swap : Certified (graph core2287) (root 9) 4 0 :=
  of_native_maps core2287 DegreeTwoThreeSpectrum4584.graph DegreeTwoThreeSpectrum4070.graph
    sourceMap2287swap fusedMap2287swap sourceMap2287swap_checked fusedMap2287swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2287
#print axioms sourceMap2287swap_checked
#print axioms fusedMap2287swap_checked
#print axioms certified2287swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
