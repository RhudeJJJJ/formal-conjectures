/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2273 : Family 9 := level9.get ⟨220,by decide⟩
def sourceMap2273 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2273 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2273_checked : acceptsGraphIso
    (source (graph core2273) (root 9) 0 4) DegreeTwoThreeSpectrum4471.graph sourceMap2273=true := by decide +kernel
theorem fusedMap2273_checked : acceptsGraphIso
    (fused (graph core2273) (root 9) 0 4) DegreeTwoThreeSpectrum4007.graph fusedMap2273=true := by decide +kernel
theorem certified2273 : Certified (graph core2273) (root 9) 0 4 :=
  of_native_maps core2273 DegreeTwoThreeSpectrum4471.graph DegreeTwoThreeSpectrum4007.graph
    sourceMap2273 fusedMap2273 sourceMap2273_checked fusedMap2273_checked
    DegreeTwoThreeFiniteComparisons.comparison2273
#print axioms sourceMap2273_checked
#print axioms fusedMap2273_checked
#print axioms certified2273
def sourceMap2273swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2273swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2273swap_checked : acceptsGraphIso
    (source (graph core2273) (root 9) 4 0) DegreeTwoThreeSpectrum4471.graph sourceMap2273swap=true := by decide +kernel
theorem fusedMap2273swap_checked : acceptsGraphIso
    (fused (graph core2273) (root 9) 4 0) DegreeTwoThreeSpectrum4007.graph fusedMap2273swap=true := by decide +kernel
theorem certified2273swap : Certified (graph core2273) (root 9) 4 0 :=
  of_native_maps core2273 DegreeTwoThreeSpectrum4471.graph DegreeTwoThreeSpectrum4007.graph
    sourceMap2273swap fusedMap2273swap sourceMap2273swap_checked fusedMap2273swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2273
#print axioms sourceMap2273swap_checked
#print axioms fusedMap2273swap_checked
#print axioms certified2273swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
