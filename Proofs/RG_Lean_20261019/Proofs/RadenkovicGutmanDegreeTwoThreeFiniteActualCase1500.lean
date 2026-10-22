/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1500 : Family 10 := level10.get ⟨289,by decide⟩
def sourceMap1500 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1500 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1500_checked : acceptsGraphIso
    (source (graph core1500) (root 10) 0 2) DegreeTwoThreeSpectrum2658.graph sourceMap1500=true := by decide +kernel
theorem fusedMap1500_checked : acceptsGraphIso
    (fused (graph core1500) (root 10) 0 2) DegreeTwoThreeSpectrum2660.graph fusedMap1500=true := by decide +kernel
theorem certified1500 : Certified (graph core1500) (root 10) 0 2 :=
  of_native_maps core1500 DegreeTwoThreeSpectrum2658.graph DegreeTwoThreeSpectrum2660.graph
    sourceMap1500 fusedMap1500 sourceMap1500_checked fusedMap1500_checked
    DegreeTwoThreeFiniteComparisons.comparison1500
#print axioms sourceMap1500_checked
#print axioms fusedMap1500_checked
#print axioms certified1500
def sourceMap1500swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1500swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1500swap_checked : acceptsGraphIso
    (source (graph core1500) (root 10) 2 0) DegreeTwoThreeSpectrum2658.graph sourceMap1500swap=true := by decide +kernel
theorem fusedMap1500swap_checked : acceptsGraphIso
    (fused (graph core1500) (root 10) 2 0) DegreeTwoThreeSpectrum2660.graph fusedMap1500swap=true := by decide +kernel
theorem certified1500swap : Certified (graph core1500) (root 10) 2 0 :=
  of_native_maps core1500 DegreeTwoThreeSpectrum2658.graph DegreeTwoThreeSpectrum2660.graph
    sourceMap1500swap fusedMap1500swap sourceMap1500swap_checked fusedMap1500swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1500
#print axioms sourceMap1500swap_checked
#print axioms fusedMap1500swap_checked
#print axioms certified1500swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
