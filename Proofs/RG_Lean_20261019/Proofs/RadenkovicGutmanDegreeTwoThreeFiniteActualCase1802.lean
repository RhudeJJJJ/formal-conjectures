/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1802 : Family 10 := level10.get ⟨1140,by decide⟩
def sourceMap1802 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1802 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1802_checked : acceptsGraphIso
    (source (graph core1802) (root 10) 0 2) DegreeTwoThreeSpectrum3226.graph sourceMap1802=true := by decide +kernel
theorem fusedMap1802_checked : acceptsGraphIso
    (fused (graph core1802) (root 10) 0 2) DegreeTwoThreeSpectrum3228.graph fusedMap1802=true := by decide +kernel
theorem certified1802 : Certified (graph core1802) (root 10) 0 2 :=
  of_native_maps core1802 DegreeTwoThreeSpectrum3226.graph DegreeTwoThreeSpectrum3228.graph
    sourceMap1802 fusedMap1802 sourceMap1802_checked fusedMap1802_checked
    DegreeTwoThreeFiniteComparisons.comparison1802
#print axioms sourceMap1802_checked
#print axioms fusedMap1802_checked
#print axioms certified1802
def sourceMap1802swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1802swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1802swap_checked : acceptsGraphIso
    (source (graph core1802) (root 10) 2 0) DegreeTwoThreeSpectrum3226.graph sourceMap1802swap=true := by decide +kernel
theorem fusedMap1802swap_checked : acceptsGraphIso
    (fused (graph core1802) (root 10) 2 0) DegreeTwoThreeSpectrum3228.graph fusedMap1802swap=true := by decide +kernel
theorem certified1802swap : Certified (graph core1802) (root 10) 2 0 :=
  of_native_maps core1802 DegreeTwoThreeSpectrum3226.graph DegreeTwoThreeSpectrum3228.graph
    sourceMap1802swap fusedMap1802swap sourceMap1802swap_checked fusedMap1802swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1802
#print axioms sourceMap1802swap_checked
#print axioms fusedMap1802swap_checked
#print axioms certified1802swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
