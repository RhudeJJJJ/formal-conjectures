/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3068 : Family 10 := level10.get ⟨1755,by decide⟩
def sourceMap3068 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3068 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3068_checked : acceptsGraphIso
    (source (graph core3068) (root 10) 0 4) DegreeTwoThreeSpectrum7404.graph sourceMap3068=true := by decide +kernel
theorem fusedMap3068_checked : acceptsGraphIso
    (fused (graph core3068) (root 10) 0 4) DegreeTwoThreeSpectrum6627.graph fusedMap3068=true := by decide +kernel
theorem certified3068 : Certified (graph core3068) (root 10) 0 4 :=
  of_native_maps core3068 DegreeTwoThreeSpectrum7404.graph DegreeTwoThreeSpectrum6627.graph
    sourceMap3068 fusedMap3068 sourceMap3068_checked fusedMap3068_checked
    DegreeTwoThreeFiniteComparisons.comparison3068
#print axioms sourceMap3068_checked
#print axioms fusedMap3068_checked
#print axioms certified3068
def sourceMap3068swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3068swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3068swap_checked : acceptsGraphIso
    (source (graph core3068) (root 10) 4 0) DegreeTwoThreeSpectrum7404.graph sourceMap3068swap=true := by decide +kernel
theorem fusedMap3068swap_checked : acceptsGraphIso
    (fused (graph core3068) (root 10) 4 0) DegreeTwoThreeSpectrum6627.graph fusedMap3068swap=true := by decide +kernel
theorem certified3068swap : Certified (graph core3068) (root 10) 4 0 :=
  of_native_maps core3068 DegreeTwoThreeSpectrum7404.graph DegreeTwoThreeSpectrum6627.graph
    sourceMap3068swap fusedMap3068swap sourceMap3068swap_checked fusedMap3068swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3068
#print axioms sourceMap3068swap_checked
#print axioms fusedMap3068swap_checked
#print axioms certified3068swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
