/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1447 : Family 10 := level10.get ⟨92,by decide⟩
def sourceMap1447 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1447 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1447_checked : acceptsGraphIso
    (source (graph core1447) (root 10) 0 2) DegreeTwoThreeSpectrum2684.graph sourceMap1447=true := by decide +kernel
theorem fusedMap1447_checked : acceptsGraphIso
    (fused (graph core1447) (root 10) 0 2) DegreeTwoThreeSpectrum2353.graph fusedMap1447=true := by decide +kernel
theorem certified1447 : Certified (graph core1447) (root 10) 0 2 :=
  of_native_maps core1447 DegreeTwoThreeSpectrum2684.graph DegreeTwoThreeSpectrum2353.graph
    sourceMap1447 fusedMap1447 sourceMap1447_checked fusedMap1447_checked
    DegreeTwoThreeFiniteComparisons.comparison1447
#print axioms sourceMap1447_checked
#print axioms fusedMap1447_checked
#print axioms certified1447
def sourceMap1447swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1447swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1447swap_checked : acceptsGraphIso
    (source (graph core1447) (root 10) 2 0) DegreeTwoThreeSpectrum2684.graph sourceMap1447swap=true := by decide +kernel
theorem fusedMap1447swap_checked : acceptsGraphIso
    (fused (graph core1447) (root 10) 2 0) DegreeTwoThreeSpectrum2353.graph fusedMap1447swap=true := by decide +kernel
theorem certified1447swap : Certified (graph core1447) (root 10) 2 0 :=
  of_native_maps core1447 DegreeTwoThreeSpectrum2684.graph DegreeTwoThreeSpectrum2353.graph
    sourceMap1447swap fusedMap1447swap sourceMap1447swap_checked fusedMap1447swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1447
#print axioms sourceMap1447swap_checked
#print axioms fusedMap1447swap_checked
#print axioms certified1447swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
