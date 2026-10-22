/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1273 : Family 9 := level9.get ⟨283,by decide⟩
def sourceMap1273 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,2,3,4,8,5,6,7] (sourceLabel 9 0 2 v)
def fusedMap1273 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,7,8,9,10] (fusedLabel 9 0 2 v)
theorem sourceMap1273_checked : acceptsGraphIso
    (source (graph core1273) (root 9) 0 2) DegreeTwoThreeSpectrum2185.graph sourceMap1273=true := by decide +kernel
theorem fusedMap1273_checked : acceptsGraphIso
    (fused (graph core1273) (root 9) 0 2) DegreeTwoThreeSpectrum1897.graph fusedMap1273=true := by decide +kernel
theorem certified1273 : Certified (graph core1273) (root 9) 0 2 :=
  of_native_maps core1273 DegreeTwoThreeSpectrum2185.graph DegreeTwoThreeSpectrum1897.graph
    sourceMap1273 fusedMap1273 sourceMap1273_checked fusedMap1273_checked
    DegreeTwoThreeFiniteComparisons.comparison1273
#print axioms sourceMap1273_checked
#print axioms fusedMap1273_checked
#print axioms certified1273
def sourceMap1273swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,2,3,4,5,6,7,8] (sourceLabel 9 2 0 v)
def fusedMap1273swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,7,8,9,10] (fusedLabel 9 2 0 v)
theorem sourceMap1273swap_checked : acceptsGraphIso
    (source (graph core1273) (root 9) 2 0) DegreeTwoThreeSpectrum2185.graph sourceMap1273swap=true := by decide +kernel
theorem fusedMap1273swap_checked : acceptsGraphIso
    (fused (graph core1273) (root 9) 2 0) DegreeTwoThreeSpectrum1897.graph fusedMap1273swap=true := by decide +kernel
theorem certified1273swap : Certified (graph core1273) (root 9) 2 0 :=
  of_native_maps core1273 DegreeTwoThreeSpectrum2185.graph DegreeTwoThreeSpectrum1897.graph
    sourceMap1273swap fusedMap1273swap sourceMap1273swap_checked fusedMap1273swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1273
#print axioms sourceMap1273swap_checked
#print axioms fusedMap1273swap_checked
#print axioms certified1273swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
