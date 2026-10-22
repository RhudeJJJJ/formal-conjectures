/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1540 : Family 10 := level10.get ⟨422,by decide⟩
def sourceMap1540 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,8,5,6,7,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1540 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,12,13,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1540_checked : acceptsGraphIso
    (source (graph core1540) (root 10) 0 2) DegreeTwoThreeSpectrum2846.graph sourceMap1540=true := by decide +kernel
theorem fusedMap1540_checked : acceptsGraphIso
    (fused (graph core1540) (root 10) 0 2) DegreeTwoThreeSpectrum2937.graph fusedMap1540=true := by decide +kernel
theorem certified1540 : Certified (graph core1540) (root 10) 0 2 :=
  of_native_maps core1540 DegreeTwoThreeSpectrum2846.graph DegreeTwoThreeSpectrum2937.graph
    sourceMap1540 fusedMap1540 sourceMap1540_checked fusedMap1540_checked
    DegreeTwoThreeFiniteComparisons.comparison1540
#print axioms sourceMap1540_checked
#print axioms fusedMap1540_checked
#print axioms certified1540
def sourceMap1540swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,8,5,6,2,3,4,7] (sourceLabel 10 2 0 v)
def fusedMap1540swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,12,13,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1540swap_checked : acceptsGraphIso
    (source (graph core1540) (root 10) 2 0) DegreeTwoThreeSpectrum2846.graph sourceMap1540swap=true := by decide +kernel
theorem fusedMap1540swap_checked : acceptsGraphIso
    (fused (graph core1540) (root 10) 2 0) DegreeTwoThreeSpectrum2937.graph fusedMap1540swap=true := by decide +kernel
theorem certified1540swap : Certified (graph core1540) (root 10) 2 0 :=
  of_native_maps core1540 DegreeTwoThreeSpectrum2846.graph DegreeTwoThreeSpectrum2937.graph
    sourceMap1540swap fusedMap1540swap sourceMap1540swap_checked fusedMap1540swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1540
#print axioms sourceMap1540swap_checked
#print axioms fusedMap1540swap_checked
#print axioms certified1540swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
