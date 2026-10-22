/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1244 : Family 9 := level9.get ⟨196,by decide⟩
def sourceMap1244 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,13,7,8,9] (sourceLabel 9 0 2 v)
def fusedMap1244 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,7,8,9,10] (fusedLabel 9 0 2 v)
theorem sourceMap1244_checked : acceptsGraphIso
    (source (graph core1244) (root 9) 0 2) DegreeTwoThreeSpectrum2070.graph sourceMap1244=true := by decide +kernel
theorem fusedMap1244_checked : acceptsGraphIso
    (fused (graph core1244) (root 9) 0 2) DegreeTwoThreeSpectrum1800.graph fusedMap1244=true := by decide +kernel
theorem certified1244 : Certified (graph core1244) (root 9) 0 2 :=
  of_native_maps core1244 DegreeTwoThreeSpectrum2070.graph DegreeTwoThreeSpectrum1800.graph
    sourceMap1244 fusedMap1244 sourceMap1244_checked fusedMap1244_checked
    DegreeTwoThreeFiniteComparisons.comparison1244
#print axioms sourceMap1244_checked
#print axioms fusedMap1244_checked
#print axioms certified1244
def sourceMap1244swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9,13] (sourceLabel 9 2 0 v)
def fusedMap1244swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,7,8,9,10] (fusedLabel 9 2 0 v)
theorem sourceMap1244swap_checked : acceptsGraphIso
    (source (graph core1244) (root 9) 2 0) DegreeTwoThreeSpectrum2070.graph sourceMap1244swap=true := by decide +kernel
theorem fusedMap1244swap_checked : acceptsGraphIso
    (fused (graph core1244) (root 9) 2 0) DegreeTwoThreeSpectrum1800.graph fusedMap1244swap=true := by decide +kernel
theorem certified1244swap : Certified (graph core1244) (root 9) 2 0 :=
  of_native_maps core1244 DegreeTwoThreeSpectrum2070.graph DegreeTwoThreeSpectrum1800.graph
    sourceMap1244swap fusedMap1244swap sourceMap1244swap_checked fusedMap1244swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1244
#print axioms sourceMap1244swap_checked
#print axioms fusedMap1244swap_checked
#print axioms certified1244swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
