/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1277 : Family 9 := level9.get ⟨297,by decide⟩
def sourceMap1277 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,5,6,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1277 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1277_checked : acceptsGraphIso
    (source (graph core1277) (root 9) 0 2) DegreeTwoThreeSpectrum2227.graph sourceMap1277=true := by decide +kernel
theorem fusedMap1277_checked : acceptsGraphIso
    (fused (graph core1277) (root 9) 0 2) DegreeTwoThreeSpectrum1913.graph fusedMap1277=true := by decide +kernel
theorem certified1277 : Certified (graph core1277) (root 9) 0 2 :=
  of_native_maps core1277 DegreeTwoThreeSpectrum2227.graph DegreeTwoThreeSpectrum1913.graph
    sourceMap1277 fusedMap1277 sourceMap1277_checked fusedMap1277_checked
    DegreeTwoThreeFiniteComparisons.comparison1277
#print axioms sourceMap1277_checked
#print axioms fusedMap1277_checked
#print axioms certified1277
def sourceMap1277swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,5,2,3,4,6] (sourceLabel 9 2 0 v)
def fusedMap1277swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1277swap_checked : acceptsGraphIso
    (source (graph core1277) (root 9) 2 0) DegreeTwoThreeSpectrum2227.graph sourceMap1277swap=true := by decide +kernel
theorem fusedMap1277swap_checked : acceptsGraphIso
    (fused (graph core1277) (root 9) 2 0) DegreeTwoThreeSpectrum1913.graph fusedMap1277swap=true := by decide +kernel
theorem certified1277swap : Certified (graph core1277) (root 9) 2 0 :=
  of_native_maps core1277 DegreeTwoThreeSpectrum2227.graph DegreeTwoThreeSpectrum1913.graph
    sourceMap1277swap fusedMap1277swap sourceMap1277swap_checked fusedMap1277swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1277
#print axioms sourceMap1277swap_checked
#print axioms fusedMap1277swap_checked
#print axioms certified1277swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
