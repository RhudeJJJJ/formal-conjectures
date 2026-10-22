/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1463 : Family 10 := level10.get ⟨161,by decide⟩
def sourceMap1463 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,9,10,11,12,13,14,8,6,7,3,4,5] (sourceLabel 10 0 2 v)
def fusedMap1463 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,7,6,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1463_checked : acceptsGraphIso
    (source (graph core1463) (root 10) 0 2) DegreeTwoThreeSpectrum2894.graph sourceMap1463=true := by decide +kernel
theorem fusedMap1463_checked : acceptsGraphIso
    (fused (graph core1463) (root 10) 0 2) DegreeTwoThreeSpectrum2420.graph fusedMap1463=true := by decide +kernel
theorem certified1463 : Certified (graph core1463) (root 10) 0 2 :=
  of_native_maps core1463 DegreeTwoThreeSpectrum2894.graph DegreeTwoThreeSpectrum2420.graph
    sourceMap1463 fusedMap1463 sourceMap1463_checked fusedMap1463_checked
    DegreeTwoThreeFiniteComparisons.comparison1463
#print axioms sourceMap1463_checked
#print axioms fusedMap1463_checked
#print axioms certified1463
def sourceMap1463swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,1,0,9,10,11,12,13,14,8,6,3,4,5,7] (sourceLabel 10 2 0 v)
def fusedMap1463swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,7,6,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1463swap_checked : acceptsGraphIso
    (source (graph core1463) (root 10) 2 0) DegreeTwoThreeSpectrum2894.graph sourceMap1463swap=true := by decide +kernel
theorem fusedMap1463swap_checked : acceptsGraphIso
    (fused (graph core1463) (root 10) 2 0) DegreeTwoThreeSpectrum2420.graph fusedMap1463swap=true := by decide +kernel
theorem certified1463swap : Certified (graph core1463) (root 10) 2 0 :=
  of_native_maps core1463 DegreeTwoThreeSpectrum2894.graph DegreeTwoThreeSpectrum2420.graph
    sourceMap1463swap fusedMap1463swap sourceMap1463swap_checked fusedMap1463swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1463
#print axioms sourceMap1463swap_checked
#print axioms fusedMap1463swap_checked
#print axioms certified1463swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
