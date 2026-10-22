/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1335 : Family 9 := level9.get ⟨444,by decide⟩
def sourceMap1335 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1335 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1335_checked : acceptsGraphIso
    (source (graph core1335) (root 9) 0 2) DegreeTwoThreeSpectrum2121.graph sourceMap1335=true := by decide +kernel
theorem fusedMap1335_checked : acceptsGraphIso
    (fused (graph core1335) (root 9) 0 2) DegreeTwoThreeSpectrum2123.graph fusedMap1335=true := by decide +kernel
theorem certified1335 : Certified (graph core1335) (root 9) 0 2 :=
  of_native_maps core1335 DegreeTwoThreeSpectrum2121.graph DegreeTwoThreeSpectrum2123.graph
    sourceMap1335 fusedMap1335 sourceMap1335_checked fusedMap1335_checked
    DegreeTwoThreeFiniteComparisons.comparison1335
#print axioms sourceMap1335_checked
#print axioms fusedMap1335_checked
#print axioms certified1335
def sourceMap1335swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1335swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1335swap_checked : acceptsGraphIso
    (source (graph core1335) (root 9) 2 0) DegreeTwoThreeSpectrum2121.graph sourceMap1335swap=true := by decide +kernel
theorem fusedMap1335swap_checked : acceptsGraphIso
    (fused (graph core1335) (root 9) 2 0) DegreeTwoThreeSpectrum2123.graph fusedMap1335swap=true := by decide +kernel
theorem certified1335swap : Certified (graph core1335) (root 9) 2 0 :=
  of_native_maps core1335 DegreeTwoThreeSpectrum2121.graph DegreeTwoThreeSpectrum2123.graph
    sourceMap1335swap fusedMap1335swap sourceMap1335swap_checked fusedMap1335swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1335
#print axioms sourceMap1335swap_checked
#print axioms fusedMap1335swap_checked
#print axioms certified1335swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
