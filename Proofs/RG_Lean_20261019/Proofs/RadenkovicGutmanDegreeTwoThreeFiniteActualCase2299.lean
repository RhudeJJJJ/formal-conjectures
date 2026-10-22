/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2299 : Family 9 := level9.get ⟨294,by decide⟩
def sourceMap2299 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2299 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2299_checked : acceptsGraphIso
    (source (graph core2299) (root 9) 0 4) DegreeTwoThreeSpectrum4650.graph sourceMap2299=true := by decide +kernel
theorem fusedMap2299_checked : acceptsGraphIso
    (fused (graph core2299) (root 9) 0 4) DegreeTwoThreeSpectrum4123.graph fusedMap2299=true := by decide +kernel
theorem certified2299 : Certified (graph core2299) (root 9) 0 4 :=
  of_native_maps core2299 DegreeTwoThreeSpectrum4650.graph DegreeTwoThreeSpectrum4123.graph
    sourceMap2299 fusedMap2299 sourceMap2299_checked fusedMap2299_checked
    DegreeTwoThreeFiniteComparisons.comparison2299
#print axioms sourceMap2299_checked
#print axioms fusedMap2299_checked
#print axioms certified2299
def sourceMap2299swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2299swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2299swap_checked : acceptsGraphIso
    (source (graph core2299) (root 9) 4 0) DegreeTwoThreeSpectrum4650.graph sourceMap2299swap=true := by decide +kernel
theorem fusedMap2299swap_checked : acceptsGraphIso
    (fused (graph core2299) (root 9) 4 0) DegreeTwoThreeSpectrum4123.graph fusedMap2299swap=true := by decide +kernel
theorem certified2299swap : Certified (graph core2299) (root 9) 4 0 :=
  of_native_maps core2299 DegreeTwoThreeSpectrum4650.graph DegreeTwoThreeSpectrum4123.graph
    sourceMap2299swap fusedMap2299swap sourceMap2299swap_checked fusedMap2299swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2299
#print axioms sourceMap2299swap_checked
#print axioms fusedMap2299swap_checked
#print axioms certified2299swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
