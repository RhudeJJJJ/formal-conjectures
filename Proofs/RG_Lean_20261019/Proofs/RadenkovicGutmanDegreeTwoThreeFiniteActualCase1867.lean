/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1867 : Family 10 := level10.get ⟨1292,by decide⟩
def sourceMap1867 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,13,14,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1867 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1867_checked : acceptsGraphIso
    (source (graph core1867) (root 10) 0 2) DegreeTwoThreeSpectrum3449.graph sourceMap1867=true := by decide +kernel
theorem fusedMap1867_checked : acceptsGraphIso
    (fused (graph core1867) (root 10) 0 2) DegreeTwoThreeSpectrum3458.graph fusedMap1867=true := by decide +kernel
theorem certified1867 : Certified (graph core1867) (root 10) 0 2 :=
  of_native_maps core1867 DegreeTwoThreeSpectrum3449.graph DegreeTwoThreeSpectrum3458.graph
    sourceMap1867 fusedMap1867 sourceMap1867_checked fusedMap1867_checked
    DegreeTwoThreeFiniteComparisons.comparison1867
#print axioms sourceMap1867_checked
#print axioms fusedMap1867_checked
#print axioms certified1867
def sourceMap1867swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,13,7,8,9,14] (sourceLabel 10 2 0 v)
def fusedMap1867swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1867swap_checked : acceptsGraphIso
    (source (graph core1867) (root 10) 2 0) DegreeTwoThreeSpectrum3449.graph sourceMap1867swap=true := by decide +kernel
theorem fusedMap1867swap_checked : acceptsGraphIso
    (fused (graph core1867) (root 10) 2 0) DegreeTwoThreeSpectrum3458.graph fusedMap1867swap=true := by decide +kernel
theorem certified1867swap : Certified (graph core1867) (root 10) 2 0 :=
  of_native_maps core1867 DegreeTwoThreeSpectrum3449.graph DegreeTwoThreeSpectrum3458.graph
    sourceMap1867swap fusedMap1867swap sourceMap1867swap_checked fusedMap1867swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1867
#print axioms sourceMap1867swap_checked
#print axioms fusedMap1867swap_checked
#print axioms certified1867swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
