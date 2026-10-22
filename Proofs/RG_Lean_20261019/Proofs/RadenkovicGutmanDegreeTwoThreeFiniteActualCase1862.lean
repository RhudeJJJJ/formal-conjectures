/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1862 : Family 10 := level10.get ⟨1284,by decide⟩
def sourceMap1862 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1862 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1862_checked : acceptsGraphIso
    (source (graph core1862) (root 10) 0 2) DegreeTwoThreeSpectrum3440.graph sourceMap1862=true := by decide +kernel
theorem fusedMap1862_checked : acceptsGraphIso
    (fused (graph core1862) (root 10) 0 2) DegreeTwoThreeSpectrum3444.graph fusedMap1862=true := by decide +kernel
theorem certified1862 : Certified (graph core1862) (root 10) 0 2 :=
  of_native_maps core1862 DegreeTwoThreeSpectrum3440.graph DegreeTwoThreeSpectrum3444.graph
    sourceMap1862 fusedMap1862 sourceMap1862_checked fusedMap1862_checked
    DegreeTwoThreeFiniteComparisons.comparison1862
#print axioms sourceMap1862_checked
#print axioms fusedMap1862_checked
#print axioms certified1862
def sourceMap1862swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1862swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1862swap_checked : acceptsGraphIso
    (source (graph core1862) (root 10) 2 0) DegreeTwoThreeSpectrum3440.graph sourceMap1862swap=true := by decide +kernel
theorem fusedMap1862swap_checked : acceptsGraphIso
    (fused (graph core1862) (root 10) 2 0) DegreeTwoThreeSpectrum3444.graph fusedMap1862swap=true := by decide +kernel
theorem certified1862swap : Certified (graph core1862) (root 10) 2 0 :=
  of_native_maps core1862 DegreeTwoThreeSpectrum3440.graph DegreeTwoThreeSpectrum3444.graph
    sourceMap1862swap fusedMap1862swap sourceMap1862swap_checked fusedMap1862swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1862
#print axioms sourceMap1862swap_checked
#print axioms fusedMap1862swap_checked
#print axioms certified1862swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
