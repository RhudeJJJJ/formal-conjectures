/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1620 : Family 10 := level10.get ⟨663,by decide⟩
def sourceMap1620 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,12,13,14,10,11,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1620 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1620_checked : acceptsGraphIso
    (source (graph core1620) (root 10) 0 2) DegreeTwoThreeSpectrum3367.graph sourceMap1620=true := by decide +kernel
theorem fusedMap1620_checked : acceptsGraphIso
    (fused (graph core1620) (root 10) 0 2) DegreeTwoThreeSpectrum2610.graph fusedMap1620=true := by decide +kernel
theorem certified1620 : Certified (graph core1620) (root 10) 0 2 :=
  of_native_maps core1620 DegreeTwoThreeSpectrum3367.graph DegreeTwoThreeSpectrum2610.graph
    sourceMap1620 fusedMap1620 sourceMap1620_checked fusedMap1620_checked
    DegreeTwoThreeFiniteComparisons.comparison1620
#print axioms sourceMap1620_checked
#print axioms fusedMap1620_checked
#print axioms certified1620
def sourceMap1620swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,12,13,14,10,7,8,9,11] (sourceLabel 10 2 0 v)
def fusedMap1620swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1620swap_checked : acceptsGraphIso
    (source (graph core1620) (root 10) 2 0) DegreeTwoThreeSpectrum3367.graph sourceMap1620swap=true := by decide +kernel
theorem fusedMap1620swap_checked : acceptsGraphIso
    (fused (graph core1620) (root 10) 2 0) DegreeTwoThreeSpectrum2610.graph fusedMap1620swap=true := by decide +kernel
theorem certified1620swap : Certified (graph core1620) (root 10) 2 0 :=
  of_native_maps core1620 DegreeTwoThreeSpectrum3367.graph DegreeTwoThreeSpectrum2610.graph
    sourceMap1620swap fusedMap1620swap sourceMap1620swap_checked fusedMap1620swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1620
#print axioms sourceMap1620swap_checked
#print axioms fusedMap1620swap_checked
#print axioms certified1620swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
