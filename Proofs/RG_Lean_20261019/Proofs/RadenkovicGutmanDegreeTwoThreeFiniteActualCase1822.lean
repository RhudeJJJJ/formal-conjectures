/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1822 : Family 10 := level10.get ⟨1191,by decide⟩
def sourceMap1822 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1822 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1822_checked : acceptsGraphIso
    (source (graph core1822) (root 10) 0 2) DegreeTwoThreeSpectrum3307.graph sourceMap1822=true := by decide +kernel
theorem fusedMap1822_checked : acceptsGraphIso
    (fused (graph core1822) (root 10) 0 2) DegreeTwoThreeSpectrum3308.graph fusedMap1822=true := by decide +kernel
theorem certified1822 : Certified (graph core1822) (root 10) 0 2 :=
  of_native_maps core1822 DegreeTwoThreeSpectrum3307.graph DegreeTwoThreeSpectrum3308.graph
    sourceMap1822 fusedMap1822 sourceMap1822_checked fusedMap1822_checked
    DegreeTwoThreeFiniteComparisons.comparison1822
#print axioms sourceMap1822_checked
#print axioms fusedMap1822_checked
#print axioms certified1822
def sourceMap1822swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1822swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1822swap_checked : acceptsGraphIso
    (source (graph core1822) (root 10) 2 0) DegreeTwoThreeSpectrum3307.graph sourceMap1822swap=true := by decide +kernel
theorem fusedMap1822swap_checked : acceptsGraphIso
    (fused (graph core1822) (root 10) 2 0) DegreeTwoThreeSpectrum3308.graph fusedMap1822swap=true := by decide +kernel
theorem certified1822swap : Certified (graph core1822) (root 10) 2 0 :=
  of_native_maps core1822 DegreeTwoThreeSpectrum3307.graph DegreeTwoThreeSpectrum3308.graph
    sourceMap1822swap fusedMap1822swap sourceMap1822swap_checked fusedMap1822swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1822
#print axioms sourceMap1822swap_checked
#print axioms fusedMap1822swap_checked
#print axioms certified1822swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
