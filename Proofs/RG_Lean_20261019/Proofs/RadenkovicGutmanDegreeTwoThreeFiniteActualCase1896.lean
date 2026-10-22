/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1896 : Family 10 := level10.get ⟨1364,by decide⟩
def sourceMap1896 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1896 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1896_checked : acceptsGraphIso
    (source (graph core1896) (root 10) 0 2) DegreeTwoThreeSpectrum3556.graph sourceMap1896=true := by decide +kernel
theorem fusedMap1896_checked : acceptsGraphIso
    (fused (graph core1896) (root 10) 0 2) DegreeTwoThreeSpectrum3558.graph fusedMap1896=true := by decide +kernel
theorem certified1896 : Certified (graph core1896) (root 10) 0 2 :=
  of_native_maps core1896 DegreeTwoThreeSpectrum3556.graph DegreeTwoThreeSpectrum3558.graph
    sourceMap1896 fusedMap1896 sourceMap1896_checked fusedMap1896_checked
    DegreeTwoThreeFiniteComparisons.comparison1896
#print axioms sourceMap1896_checked
#print axioms fusedMap1896_checked
#print axioms certified1896
def sourceMap1896swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1896swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1896swap_checked : acceptsGraphIso
    (source (graph core1896) (root 10) 2 0) DegreeTwoThreeSpectrum3556.graph sourceMap1896swap=true := by decide +kernel
theorem fusedMap1896swap_checked : acceptsGraphIso
    (fused (graph core1896) (root 10) 2 0) DegreeTwoThreeSpectrum3558.graph fusedMap1896swap=true := by decide +kernel
theorem certified1896swap : Certified (graph core1896) (root 10) 2 0 :=
  of_native_maps core1896 DegreeTwoThreeSpectrum3556.graph DegreeTwoThreeSpectrum3558.graph
    sourceMap1896swap fusedMap1896swap sourceMap1896swap_checked fusedMap1896swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1896
#print axioms sourceMap1896swap_checked
#print axioms fusedMap1896swap_checked
#print axioms certified1896swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
