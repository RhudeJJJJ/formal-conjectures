/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1817 : Family 10 := level10.get ⟨1176,by decide⟩
def sourceMap1817 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1817 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1817_checked : acceptsGraphIso
    (source (graph core1817) (root 10) 0 2) DegreeTwoThreeSpectrum3280.graph sourceMap1817=true := by decide +kernel
theorem fusedMap1817_checked : acceptsGraphIso
    (fused (graph core1817) (root 10) 0 2) DegreeTwoThreeSpectrum3281.graph fusedMap1817=true := by decide +kernel
theorem certified1817 : Certified (graph core1817) (root 10) 0 2 :=
  of_native_maps core1817 DegreeTwoThreeSpectrum3280.graph DegreeTwoThreeSpectrum3281.graph
    sourceMap1817 fusedMap1817 sourceMap1817_checked fusedMap1817_checked
    DegreeTwoThreeFiniteComparisons.comparison1817
#print axioms sourceMap1817_checked
#print axioms fusedMap1817_checked
#print axioms certified1817
def sourceMap1817swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1817swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1817swap_checked : acceptsGraphIso
    (source (graph core1817) (root 10) 2 0) DegreeTwoThreeSpectrum3280.graph sourceMap1817swap=true := by decide +kernel
theorem fusedMap1817swap_checked : acceptsGraphIso
    (fused (graph core1817) (root 10) 2 0) DegreeTwoThreeSpectrum3281.graph fusedMap1817swap=true := by decide +kernel
theorem certified1817swap : Certified (graph core1817) (root 10) 2 0 :=
  of_native_maps core1817 DegreeTwoThreeSpectrum3280.graph DegreeTwoThreeSpectrum3281.graph
    sourceMap1817swap fusedMap1817swap sourceMap1817swap_checked fusedMap1817swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1817
#print axioms sourceMap1817swap_checked
#print axioms fusedMap1817swap_checked
#print axioms certified1817swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
