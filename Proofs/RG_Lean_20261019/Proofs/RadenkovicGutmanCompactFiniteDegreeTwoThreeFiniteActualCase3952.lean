/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3952 : Family 7 := level7.get ⟨16,by decide⟩
def sourceMap3952 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,9,7,8,10,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3952 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3952_checked : acceptsGraphIso
    (source (graph core3952) (root 7) 1 5) DegreeTwoThreeSpectrum4050.graph sourceMap3952=true := by decide +kernel
theorem fusedMap3952_checked : acceptsGraphIso
    (fused (graph core3952) (root 7) 1 5) DegreeTwoThreeSpectrum3866.graph fusedMap3952=true := by decide +kernel
theorem certified3952 : Certified (graph core3952) (root 7) 1 5 :=
  of_native_maps core3952 DegreeTwoThreeSpectrum4050.graph DegreeTwoThreeSpectrum3866.graph
    sourceMap3952 fusedMap3952 sourceMap3952_checked fusedMap3952_checked
    DegreeTwoThreeFiniteComparisons.comparison3952
#print axioms sourceMap3952_checked
#print axioms fusedMap3952_checked
#print axioms certified3952
def sourceMap3952swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,12,13,14,15,7,8] (sourceLabel 7 5 1 v)
def fusedMap3952swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3952swap_checked : acceptsGraphIso
    (source (graph core3952) (root 7) 5 1) DegreeTwoThreeSpectrum4050.graph sourceMap3952swap=true := by decide +kernel
theorem fusedMap3952swap_checked : acceptsGraphIso
    (fused (graph core3952) (root 7) 5 1) DegreeTwoThreeSpectrum3866.graph fusedMap3952swap=true := by decide +kernel
theorem certified3952swap : Certified (graph core3952) (root 7) 5 1 :=
  of_native_maps core3952 DegreeTwoThreeSpectrum4050.graph DegreeTwoThreeSpectrum3866.graph
    sourceMap3952swap fusedMap3952swap sourceMap3952swap_checked fusedMap3952swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3952
#print axioms sourceMap3952swap_checked
#print axioms fusedMap3952swap_checked
#print axioms certified3952swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
