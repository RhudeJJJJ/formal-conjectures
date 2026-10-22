/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1203 : Family 9 := level9.get ⟨63,by decide⟩
def sourceMap1203 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1203 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1203_checked : acceptsGraphIso
    (source (graph core1203) (root 9) 0 2) DegreeTwoThreeSpectrum1793.graph sourceMap1203=true := by decide +kernel
theorem fusedMap1203_checked : acceptsGraphIso
    (fused (graph core1203) (root 9) 0 2) DegreeTwoThreeSpectrum1795.graph fusedMap1203=true := by decide +kernel
theorem certified1203 : Certified (graph core1203) (root 9) 0 2 :=
  of_native_maps core1203 DegreeTwoThreeSpectrum1793.graph DegreeTwoThreeSpectrum1795.graph
    sourceMap1203 fusedMap1203 sourceMap1203_checked fusedMap1203_checked
    DegreeTwoThreeFiniteComparisons.comparison1203
#print axioms sourceMap1203_checked
#print axioms fusedMap1203_checked
#print axioms certified1203
def sourceMap1203swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1203swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1203swap_checked : acceptsGraphIso
    (source (graph core1203) (root 9) 2 0) DegreeTwoThreeSpectrum1793.graph sourceMap1203swap=true := by decide +kernel
theorem fusedMap1203swap_checked : acceptsGraphIso
    (fused (graph core1203) (root 9) 2 0) DegreeTwoThreeSpectrum1795.graph fusedMap1203swap=true := by decide +kernel
theorem certified1203swap : Certified (graph core1203) (root 9) 2 0 :=
  of_native_maps core1203 DegreeTwoThreeSpectrum1793.graph DegreeTwoThreeSpectrum1795.graph
    sourceMap1203swap fusedMap1203swap sourceMap1203swap_checked fusedMap1203swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1203
#print axioms sourceMap1203swap_checked
#print axioms fusedMap1203swap_checked
#print axioms certified1203swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
