/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1202 : Family 9 := level9.get ⟨59,by decide⟩
def sourceMap1202 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1202 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1202_checked : acceptsGraphIso
    (source (graph core1202) (root 9) 0 2) DegreeTwoThreeSpectrum1785.graph sourceMap1202=true := by decide +kernel
theorem fusedMap1202_checked : acceptsGraphIso
    (fused (graph core1202) (root 9) 0 2) DegreeTwoThreeSpectrum1787.graph fusedMap1202=true := by decide +kernel
theorem certified1202 : Certified (graph core1202) (root 9) 0 2 :=
  of_native_maps core1202 DegreeTwoThreeSpectrum1785.graph DegreeTwoThreeSpectrum1787.graph
    sourceMap1202 fusedMap1202 sourceMap1202_checked fusedMap1202_checked
    DegreeTwoThreeFiniteComparisons.comparison1202
#print axioms sourceMap1202_checked
#print axioms fusedMap1202_checked
#print axioms certified1202
def sourceMap1202swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1202swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1202swap_checked : acceptsGraphIso
    (source (graph core1202) (root 9) 2 0) DegreeTwoThreeSpectrum1785.graph sourceMap1202swap=true := by decide +kernel
theorem fusedMap1202swap_checked : acceptsGraphIso
    (fused (graph core1202) (root 9) 2 0) DegreeTwoThreeSpectrum1787.graph fusedMap1202swap=true := by decide +kernel
theorem certified1202swap : Certified (graph core1202) (root 9) 2 0 :=
  of_native_maps core1202 DegreeTwoThreeSpectrum1785.graph DegreeTwoThreeSpectrum1787.graph
    sourceMap1202swap fusedMap1202swap sourceMap1202swap_checked fusedMap1202swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1202
#print axioms sourceMap1202swap_checked
#print axioms fusedMap1202swap_checked
#print axioms certified1202swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
