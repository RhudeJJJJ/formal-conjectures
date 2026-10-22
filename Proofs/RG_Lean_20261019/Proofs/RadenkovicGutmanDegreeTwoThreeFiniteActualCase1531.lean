/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1531 : Family 10 := level10.get ⟨397,by decide⟩
def sourceMap1531 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1531 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1531_checked : acceptsGraphIso
    (source (graph core1531) (root 10) 0 2) DegreeTwoThreeSpectrum2889.graph sourceMap1531=true := by decide +kernel
theorem fusedMap1531_checked : acceptsGraphIso
    (fused (graph core1531) (root 10) 0 2) DegreeTwoThreeSpectrum2894.graph fusedMap1531=true := by decide +kernel
theorem certified1531 : Certified (graph core1531) (root 10) 0 2 :=
  of_native_maps core1531 DegreeTwoThreeSpectrum2889.graph DegreeTwoThreeSpectrum2894.graph
    sourceMap1531 fusedMap1531 sourceMap1531_checked fusedMap1531_checked
    DegreeTwoThreeFiniteComparisons.comparison1531
#print axioms sourceMap1531_checked
#print axioms fusedMap1531_checked
#print axioms certified1531
def sourceMap1531swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1531swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1531swap_checked : acceptsGraphIso
    (source (graph core1531) (root 10) 2 0) DegreeTwoThreeSpectrum2889.graph sourceMap1531swap=true := by decide +kernel
theorem fusedMap1531swap_checked : acceptsGraphIso
    (fused (graph core1531) (root 10) 2 0) DegreeTwoThreeSpectrum2894.graph fusedMap1531swap=true := by decide +kernel
theorem certified1531swap : Certified (graph core1531) (root 10) 2 0 :=
  of_native_maps core1531 DegreeTwoThreeSpectrum2889.graph DegreeTwoThreeSpectrum2894.graph
    sourceMap1531swap fusedMap1531swap sourceMap1531swap_checked fusedMap1531swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1531
#print axioms sourceMap1531swap_checked
#print axioms fusedMap1531swap_checked
#print axioms certified1531swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
