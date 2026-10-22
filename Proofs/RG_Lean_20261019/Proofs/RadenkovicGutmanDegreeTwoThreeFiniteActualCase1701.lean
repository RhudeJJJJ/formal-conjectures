/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1701 : Family 10 := level10.get ⟨886,by decide⟩
def sourceMap1701 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1701 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1701_checked : acceptsGraphIso
    (source (graph core1701) (root 10) 0 2) DegreeTwoThreeSpectrum3701.graph sourceMap1701=true := by decide +kernel
theorem fusedMap1701_checked : acceptsGraphIso
    (fused (graph core1701) (root 10) 0 2) DegreeTwoThreeSpectrum2883.graph fusedMap1701=true := by decide +kernel
theorem certified1701 : Certified (graph core1701) (root 10) 0 2 :=
  of_native_maps core1701 DegreeTwoThreeSpectrum3701.graph DegreeTwoThreeSpectrum2883.graph
    sourceMap1701 fusedMap1701 sourceMap1701_checked fusedMap1701_checked
    DegreeTwoThreeFiniteComparisons.comparison1701
#print axioms sourceMap1701_checked
#print axioms fusedMap1701_checked
#print axioms certified1701
def sourceMap1701swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1701swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1701swap_checked : acceptsGraphIso
    (source (graph core1701) (root 10) 2 0) DegreeTwoThreeSpectrum3701.graph sourceMap1701swap=true := by decide +kernel
theorem fusedMap1701swap_checked : acceptsGraphIso
    (fused (graph core1701) (root 10) 2 0) DegreeTwoThreeSpectrum2883.graph fusedMap1701swap=true := by decide +kernel
theorem certified1701swap : Certified (graph core1701) (root 10) 2 0 :=
  of_native_maps core1701 DegreeTwoThreeSpectrum3701.graph DegreeTwoThreeSpectrum2883.graph
    sourceMap1701swap fusedMap1701swap sourceMap1701swap_checked fusedMap1701swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1701
#print axioms sourceMap1701swap_checked
#print axioms fusedMap1701swap_checked
#print axioms certified1701swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
