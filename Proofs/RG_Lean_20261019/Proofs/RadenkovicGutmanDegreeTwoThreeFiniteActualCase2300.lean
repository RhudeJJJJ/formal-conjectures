/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2300 : Family 9 := level9.get ⟨297,by decide⟩
def sourceMap2300 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2300 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2300_checked : acceptsGraphIso
    (source (graph core2300) (root 9) 0 4) DegreeTwoThreeSpectrum4651.graph sourceMap2300=true := by decide +kernel
theorem fusedMap2300_checked : acceptsGraphIso
    (fused (graph core2300) (root 9) 0 4) DegreeTwoThreeSpectrum4126.graph fusedMap2300=true := by decide +kernel
theorem certified2300 : Certified (graph core2300) (root 9) 0 4 :=
  of_native_maps core2300 DegreeTwoThreeSpectrum4651.graph DegreeTwoThreeSpectrum4126.graph
    sourceMap2300 fusedMap2300 sourceMap2300_checked fusedMap2300_checked
    DegreeTwoThreeFiniteComparisons.comparison2300
#print axioms sourceMap2300_checked
#print axioms fusedMap2300_checked
#print axioms certified2300
def sourceMap2300swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2300swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2300swap_checked : acceptsGraphIso
    (source (graph core2300) (root 9) 4 0) DegreeTwoThreeSpectrum4651.graph sourceMap2300swap=true := by decide +kernel
theorem fusedMap2300swap_checked : acceptsGraphIso
    (fused (graph core2300) (root 9) 4 0) DegreeTwoThreeSpectrum4126.graph fusedMap2300swap=true := by decide +kernel
theorem certified2300swap : Certified (graph core2300) (root 9) 4 0 :=
  of_native_maps core2300 DegreeTwoThreeSpectrum4651.graph DegreeTwoThreeSpectrum4126.graph
    sourceMap2300swap fusedMap2300swap sourceMap2300swap_checked fusedMap2300swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2300
#print axioms sourceMap2300swap_checked
#print axioms fusedMap2300swap_checked
#print axioms certified2300swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
