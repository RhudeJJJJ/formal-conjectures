/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2254 : Family 9 := level9.get ⟨160,by decide⟩
def sourceMap2254 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2254 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2254_checked : acceptsGraphIso
    (source (graph core2254) (root 9) 0 4) DegreeTwoThreeSpectrum4285.graph sourceMap2254=true := by decide +kernel
theorem fusedMap2254_checked : acceptsGraphIso
    (fused (graph core2254) (root 9) 0 4) DegreeTwoThreeSpectrum3921.graph fusedMap2254=true := by decide +kernel
theorem certified2254 : Certified (graph core2254) (root 9) 0 4 :=
  of_native_maps core2254 DegreeTwoThreeSpectrum4285.graph DegreeTwoThreeSpectrum3921.graph
    sourceMap2254 fusedMap2254 sourceMap2254_checked fusedMap2254_checked
    DegreeTwoThreeFiniteComparisons.comparison2254
#print axioms sourceMap2254_checked
#print axioms fusedMap2254_checked
#print axioms certified2254
def sourceMap2254swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2254swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2254swap_checked : acceptsGraphIso
    (source (graph core2254) (root 9) 4 0) DegreeTwoThreeSpectrum4285.graph sourceMap2254swap=true := by decide +kernel
theorem fusedMap2254swap_checked : acceptsGraphIso
    (fused (graph core2254) (root 9) 4 0) DegreeTwoThreeSpectrum3921.graph fusedMap2254swap=true := by decide +kernel
theorem certified2254swap : Certified (graph core2254) (root 9) 4 0 :=
  of_native_maps core2254 DegreeTwoThreeSpectrum4285.graph DegreeTwoThreeSpectrum3921.graph
    sourceMap2254swap fusedMap2254swap sourceMap2254swap_checked fusedMap2254swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2254
#print axioms sourceMap2254swap_checked
#print axioms fusedMap2254swap_checked
#print axioms certified2254swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
