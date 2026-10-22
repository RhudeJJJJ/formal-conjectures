/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1329 : Family 9 := level9.get ⟨431,by decide⟩
def sourceMap1329 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1329 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1329_checked : acceptsGraphIso
    (source (graph core1329) (root 9) 0 2) DegreeTwoThreeSpectrum2101.graph sourceMap1329=true := by decide +kernel
theorem fusedMap1329_checked : acceptsGraphIso
    (fused (graph core1329) (root 9) 0 2) DegreeTwoThreeSpectrum2102.graph fusedMap1329=true := by decide +kernel
theorem certified1329 : Certified (graph core1329) (root 9) 0 2 :=
  of_native_maps core1329 DegreeTwoThreeSpectrum2101.graph DegreeTwoThreeSpectrum2102.graph
    sourceMap1329 fusedMap1329 sourceMap1329_checked fusedMap1329_checked
    DegreeTwoThreeFiniteComparisons.comparison1329
#print axioms sourceMap1329_checked
#print axioms fusedMap1329_checked
#print axioms certified1329
def sourceMap1329swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1329swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1329swap_checked : acceptsGraphIso
    (source (graph core1329) (root 9) 2 0) DegreeTwoThreeSpectrum2101.graph sourceMap1329swap=true := by decide +kernel
theorem fusedMap1329swap_checked : acceptsGraphIso
    (fused (graph core1329) (root 9) 2 0) DegreeTwoThreeSpectrum2102.graph fusedMap1329swap=true := by decide +kernel
theorem certified1329swap : Certified (graph core1329) (root 9) 2 0 :=
  of_native_maps core1329 DegreeTwoThreeSpectrum2101.graph DegreeTwoThreeSpectrum2102.graph
    sourceMap1329swap fusedMap1329swap sourceMap1329swap_checked fusedMap1329swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1329
#print axioms sourceMap1329swap_checked
#print axioms fusedMap1329swap_checked
#print axioms certified1329swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
