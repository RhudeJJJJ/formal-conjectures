/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1680 : Family 10 := level10.get ⟨823,by decide⟩
def sourceMap1680 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,2,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1680 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1680_checked : acceptsGraphIso
    (source (graph core1680) (root 10) 0 2) DegreeTwoThreeSpectrum3534.graph sourceMap1680=true := by decide +kernel
theorem fusedMap1680_checked : acceptsGraphIso
    (fused (graph core1680) (root 10) 0 2) DegreeTwoThreeSpectrum2806.graph fusedMap1680=true := by decide +kernel
theorem certified1680 : Certified (graph core1680) (root 10) 0 2 :=
  of_native_maps core1680 DegreeTwoThreeSpectrum3534.graph DegreeTwoThreeSpectrum2806.graph
    sourceMap1680 fusedMap1680 sourceMap1680_checked fusedMap1680_checked
    DegreeTwoThreeFiniteComparisons.comparison1680
#print axioms sourceMap1680_checked
#print axioms fusedMap1680_checked
#print axioms certified1680
def sourceMap1680swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,2,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1680swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1680swap_checked : acceptsGraphIso
    (source (graph core1680) (root 10) 2 0) DegreeTwoThreeSpectrum3534.graph sourceMap1680swap=true := by decide +kernel
theorem fusedMap1680swap_checked : acceptsGraphIso
    (fused (graph core1680) (root 10) 2 0) DegreeTwoThreeSpectrum2806.graph fusedMap1680swap=true := by decide +kernel
theorem certified1680swap : Certified (graph core1680) (root 10) 2 0 :=
  of_native_maps core1680 DegreeTwoThreeSpectrum3534.graph DegreeTwoThreeSpectrum2806.graph
    sourceMap1680swap fusedMap1680swap sourceMap1680swap_checked fusedMap1680swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1680
#print axioms sourceMap1680swap_checked
#print axioms fusedMap1680swap_checked
#print axioms certified1680swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
