/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1695 : Family 10 := level10.get ⟨869,by decide⟩
def sourceMap1695 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,7,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1695 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1695_checked : acceptsGraphIso
    (source (graph core1695) (root 10) 0 2) DegreeTwoThreeSpectrum3677.graph sourceMap1695=true := by decide +kernel
theorem fusedMap1695_checked : acceptsGraphIso
    (fused (graph core1695) (root 10) 0 2) DegreeTwoThreeSpectrum2863.graph fusedMap1695=true := by decide +kernel
theorem certified1695 : Certified (graph core1695) (root 10) 0 2 :=
  of_native_maps core1695 DegreeTwoThreeSpectrum3677.graph DegreeTwoThreeSpectrum2863.graph
    sourceMap1695 fusedMap1695 sourceMap1695_checked fusedMap1695_checked
    DegreeTwoThreeFiniteComparisons.comparison1695
#print axioms sourceMap1695_checked
#print axioms fusedMap1695_checked
#print axioms certified1695
def sourceMap1695swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,2,3,4,7] (sourceLabel 10 2 0 v)
def fusedMap1695swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1695swap_checked : acceptsGraphIso
    (source (graph core1695) (root 10) 2 0) DegreeTwoThreeSpectrum3677.graph sourceMap1695swap=true := by decide +kernel
theorem fusedMap1695swap_checked : acceptsGraphIso
    (fused (graph core1695) (root 10) 2 0) DegreeTwoThreeSpectrum2863.graph fusedMap1695swap=true := by decide +kernel
theorem certified1695swap : Certified (graph core1695) (root 10) 2 0 :=
  of_native_maps core1695 DegreeTwoThreeSpectrum3677.graph DegreeTwoThreeSpectrum2863.graph
    sourceMap1695swap fusedMap1695swap sourceMap1695swap_checked fusedMap1695swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1695
#print axioms sourceMap1695swap_checked
#print axioms fusedMap1695swap_checked
#print axioms certified1695swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
