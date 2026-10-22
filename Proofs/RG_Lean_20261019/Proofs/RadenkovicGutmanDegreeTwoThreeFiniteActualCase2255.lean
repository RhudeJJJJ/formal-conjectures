/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2255 : Family 9 := level9.get ⟨164,by decide⟩
def sourceMap2255 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2255 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2255_checked : acceptsGraphIso
    (source (graph core2255) (root 9) 0 4) DegreeTwoThreeSpectrum4302.graph sourceMap2255=true := by decide +kernel
theorem fusedMap2255_checked : acceptsGraphIso
    (fused (graph core2255) (root 9) 0 4) DegreeTwoThreeSpectrum3925.graph fusedMap2255=true := by decide +kernel
theorem certified2255 : Certified (graph core2255) (root 9) 0 4 :=
  of_native_maps core2255 DegreeTwoThreeSpectrum4302.graph DegreeTwoThreeSpectrum3925.graph
    sourceMap2255 fusedMap2255 sourceMap2255_checked fusedMap2255_checked
    DegreeTwoThreeFiniteComparisons.comparison2255
#print axioms sourceMap2255_checked
#print axioms fusedMap2255_checked
#print axioms certified2255
def sourceMap2255swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2255swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2255swap_checked : acceptsGraphIso
    (source (graph core2255) (root 9) 4 0) DegreeTwoThreeSpectrum4302.graph sourceMap2255swap=true := by decide +kernel
theorem fusedMap2255swap_checked : acceptsGraphIso
    (fused (graph core2255) (root 9) 4 0) DegreeTwoThreeSpectrum3925.graph fusedMap2255swap=true := by decide +kernel
theorem certified2255swap : Certified (graph core2255) (root 9) 4 0 :=
  of_native_maps core2255 DegreeTwoThreeSpectrum4302.graph DegreeTwoThreeSpectrum3925.graph
    sourceMap2255swap fusedMap2255swap sourceMap2255swap_checked fusedMap2255swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2255
#print axioms sourceMap2255swap_checked
#print axioms fusedMap2255swap_checked
#print axioms certified2255swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
