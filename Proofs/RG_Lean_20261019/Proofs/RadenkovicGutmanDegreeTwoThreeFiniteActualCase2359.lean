/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2359 : Family 9 := level9.get ⟨449,by decide⟩
def sourceMap2359 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2359 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2359_checked : acceptsGraphIso
    (source (graph core2359) (root 9) 0 4) DegreeTwoThreeSpectrum4464.graph sourceMap2359=true := by decide +kernel
theorem fusedMap2359_checked : acceptsGraphIso
    (fused (graph core2359) (root 9) 0 4) DegreeTwoThreeSpectrum4465.graph fusedMap2359=true := by decide +kernel
theorem certified2359 : Certified (graph core2359) (root 9) 0 4 :=
  of_native_maps core2359 DegreeTwoThreeSpectrum4464.graph DegreeTwoThreeSpectrum4465.graph
    sourceMap2359 fusedMap2359 sourceMap2359_checked fusedMap2359_checked
    DegreeTwoThreeFiniteComparisons.comparison2359
#print axioms sourceMap2359_checked
#print axioms fusedMap2359_checked
#print axioms certified2359
def sourceMap2359swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2359swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2359swap_checked : acceptsGraphIso
    (source (graph core2359) (root 9) 4 0) DegreeTwoThreeSpectrum4464.graph sourceMap2359swap=true := by decide +kernel
theorem fusedMap2359swap_checked : acceptsGraphIso
    (fused (graph core2359) (root 9) 4 0) DegreeTwoThreeSpectrum4465.graph fusedMap2359swap=true := by decide +kernel
theorem certified2359swap : Certified (graph core2359) (root 9) 4 0 :=
  of_native_maps core2359 DegreeTwoThreeSpectrum4464.graph DegreeTwoThreeSpectrum4465.graph
    sourceMap2359swap fusedMap2359swap sourceMap2359swap_checked fusedMap2359swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2359
#print axioms sourceMap2359swap_checked
#print axioms fusedMap2359swap_checked
#print axioms certified2359swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
