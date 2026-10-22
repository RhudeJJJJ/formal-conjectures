/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2265 : Family 9 := level9.get ⟨193,by decide⟩
def sourceMap2265 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12] (sourceLabel 9 0 4 v)
def fusedMap2265 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2265_checked : acceptsGraphIso
    (source (graph core2265) (root 9) 0 4) DegreeTwoThreeSpectrum4384.graph sourceMap2265=true := by decide +kernel
theorem fusedMap2265_checked : acceptsGraphIso
    (fused (graph core2265) (root 9) 0 4) DegreeTwoThreeSpectrum3966.graph fusedMap2265=true := by decide +kernel
theorem certified2265 : Certified (graph core2265) (root 9) 0 4 :=
  of_native_maps core2265 DegreeTwoThreeSpectrum4384.graph DegreeTwoThreeSpectrum3966.graph
    sourceMap2265 fusedMap2265 sourceMap2265_checked fusedMap2265_checked
    DegreeTwoThreeFiniteComparisons.comparison2265
#print axioms sourceMap2265_checked
#print axioms fusedMap2265_checked
#print axioms certified2265
def sourceMap2265swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12,15] (sourceLabel 9 4 0 v)
def fusedMap2265swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2265swap_checked : acceptsGraphIso
    (source (graph core2265) (root 9) 4 0) DegreeTwoThreeSpectrum4384.graph sourceMap2265swap=true := by decide +kernel
theorem fusedMap2265swap_checked : acceptsGraphIso
    (fused (graph core2265) (root 9) 4 0) DegreeTwoThreeSpectrum3966.graph fusedMap2265swap=true := by decide +kernel
theorem certified2265swap : Certified (graph core2265) (root 9) 4 0 :=
  of_native_maps core2265 DegreeTwoThreeSpectrum4384.graph DegreeTwoThreeSpectrum3966.graph
    sourceMap2265swap fusedMap2265swap sourceMap2265swap_checked fusedMap2265swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2265
#print axioms sourceMap2265swap_checked
#print axioms fusedMap2265swap_checked
#print axioms certified2265swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
