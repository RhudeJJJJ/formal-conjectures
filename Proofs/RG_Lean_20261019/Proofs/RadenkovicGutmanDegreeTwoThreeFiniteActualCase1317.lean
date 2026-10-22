/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1317 : Family 9 := level9.get ⟨400,by decide⟩
def sourceMap1317 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1317 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1317_checked : acceptsGraphIso
    (source (graph core1317) (root 9) 0 2) DegreeTwoThreeSpectrum2057.graph sourceMap1317=true := by decide +kernel
theorem fusedMap1317_checked : acceptsGraphIso
    (fused (graph core1317) (root 9) 0 2) DegreeTwoThreeSpectrum2059.graph fusedMap1317=true := by decide +kernel
theorem certified1317 : Certified (graph core1317) (root 9) 0 2 :=
  of_native_maps core1317 DegreeTwoThreeSpectrum2057.graph DegreeTwoThreeSpectrum2059.graph
    sourceMap1317 fusedMap1317 sourceMap1317_checked fusedMap1317_checked
    DegreeTwoThreeFiniteComparisons.comparison1317
#print axioms sourceMap1317_checked
#print axioms fusedMap1317_checked
#print axioms certified1317
def sourceMap1317swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1317swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1317swap_checked : acceptsGraphIso
    (source (graph core1317) (root 9) 2 0) DegreeTwoThreeSpectrum2057.graph sourceMap1317swap=true := by decide +kernel
theorem fusedMap1317swap_checked : acceptsGraphIso
    (fused (graph core1317) (root 9) 2 0) DegreeTwoThreeSpectrum2059.graph fusedMap1317swap=true := by decide +kernel
theorem certified1317swap : Certified (graph core1317) (root 9) 2 0 :=
  of_native_maps core1317 DegreeTwoThreeSpectrum2057.graph DegreeTwoThreeSpectrum2059.graph
    sourceMap1317swap fusedMap1317swap sourceMap1317swap_checked fusedMap1317swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1317
#print axioms sourceMap1317swap_checked
#print axioms fusedMap1317swap_checked
#print axioms certified1317swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
