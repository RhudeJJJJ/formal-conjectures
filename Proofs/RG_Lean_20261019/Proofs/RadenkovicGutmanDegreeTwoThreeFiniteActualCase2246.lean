/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2246 : Family 9 := level9.get ⟨131,by decide⟩
def sourceMap2246 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,9,10,11,12,13,14,15,6,7,8,1,2,3,4,5] (sourceLabel 9 0 4 v)
def fusedMap2246 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (fusedLabel 9 0 4 v)
theorem sourceMap2246_checked : acceptsGraphIso
    (source (graph core2246) (root 9) 0 4) DegreeTwoThreeSpectrum4159.graph sourceMap2246=true := by decide +kernel
theorem fusedMap2246_checked : acceptsGraphIso
    (fused (graph core2246) (root 9) 0 4) DegreeTwoThreeSpectrum4166.graph fusedMap2246=true := by decide +kernel
theorem certified2246 : Certified (graph core2246) (root 9) 0 4 :=
  of_native_maps core2246 DegreeTwoThreeSpectrum4159.graph DegreeTwoThreeSpectrum4166.graph
    sourceMap2246 fusedMap2246 sourceMap2246_checked fusedMap2246_checked
    DegreeTwoThreeFiniteComparisons.comparison2246
#print axioms sourceMap2246_checked
#print axioms fusedMap2246_checked
#print axioms certified2246
def sourceMap2246swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,9,10,11,12,13,14,15,6,7,1,2,3,4,5,8] (sourceLabel 9 4 0 v)
def fusedMap2246swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (fusedLabel 9 4 0 v)
theorem sourceMap2246swap_checked : acceptsGraphIso
    (source (graph core2246) (root 9) 4 0) DegreeTwoThreeSpectrum4159.graph sourceMap2246swap=true := by decide +kernel
theorem fusedMap2246swap_checked : acceptsGraphIso
    (fused (graph core2246) (root 9) 4 0) DegreeTwoThreeSpectrum4166.graph fusedMap2246swap=true := by decide +kernel
theorem certified2246swap : Certified (graph core2246) (root 9) 4 0 :=
  of_native_maps core2246 DegreeTwoThreeSpectrum4159.graph DegreeTwoThreeSpectrum4166.graph
    sourceMap2246swap fusedMap2246swap sourceMap2246swap_checked fusedMap2246swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2246
#print axioms sourceMap2246swap_checked
#print axioms fusedMap2246swap_checked
#print axioms certified2246swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
