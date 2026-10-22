/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3244 : Family 9 := level9.get ⟨48,by decide⟩
def sourceMap3244 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3244 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3244_checked : acceptsGraphIso
    (source (graph core3244) (root 9) 0 5) DegreeTwoThreeSpectrum5223.graph sourceMap3244=true := by decide +kernel
theorem fusedMap3244_checked : acceptsGraphIso
    (fused (graph core3244) (root 9) 0 5) DegreeTwoThreeSpectrum4970.graph fusedMap3244=true := by decide +kernel
theorem certified3244 : Certified (graph core3244) (root 9) 0 5 :=
  of_native_maps core3244 DegreeTwoThreeSpectrum5223.graph DegreeTwoThreeSpectrum4970.graph
    sourceMap3244 fusedMap3244 sourceMap3244_checked fusedMap3244_checked
    DegreeTwoThreeFiniteComparisons.comparison3244
#print axioms sourceMap3244_checked
#print axioms fusedMap3244_checked
#print axioms certified3244
def sourceMap3244swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3244swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3244swap_checked : acceptsGraphIso
    (source (graph core3244) (root 9) 5 0) DegreeTwoThreeSpectrum5223.graph sourceMap3244swap=true := by decide +kernel
theorem fusedMap3244swap_checked : acceptsGraphIso
    (fused (graph core3244) (root 9) 5 0) DegreeTwoThreeSpectrum4970.graph fusedMap3244swap=true := by decide +kernel
theorem certified3244swap : Certified (graph core3244) (root 9) 5 0 :=
  of_native_maps core3244 DegreeTwoThreeSpectrum5223.graph DegreeTwoThreeSpectrum4970.graph
    sourceMap3244swap fusedMap3244swap sourceMap3244swap_checked fusedMap3244swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3244
#print axioms sourceMap3244swap_checked
#print axioms fusedMap3244swap_checked
#print axioms certified3244swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
