/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1397 : Family 9 := level9.get ⟨593,by decide⟩
def sourceMap1397 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1397 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1397_checked : acceptsGraphIso
    (source (graph core1397) (root 9) 0 2) DegreeTwoThreeSpectrum2269.graph sourceMap1397=true := by decide +kernel
theorem fusedMap1397_checked : acceptsGraphIso
    (fused (graph core1397) (root 9) 0 2) DegreeTwoThreeSpectrum1995.graph fusedMap1397=true := by decide +kernel
theorem certified1397 : Certified (graph core1397) (root 9) 0 2 :=
  of_native_maps core1397 DegreeTwoThreeSpectrum2269.graph DegreeTwoThreeSpectrum1995.graph
    sourceMap1397 fusedMap1397 sourceMap1397_checked fusedMap1397_checked
    DegreeTwoThreeFiniteComparisons.comparison1397
#print axioms sourceMap1397_checked
#print axioms fusedMap1397_checked
#print axioms certified1397
def sourceMap1397swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1397swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1397swap_checked : acceptsGraphIso
    (source (graph core1397) (root 9) 2 0) DegreeTwoThreeSpectrum2269.graph sourceMap1397swap=true := by decide +kernel
theorem fusedMap1397swap_checked : acceptsGraphIso
    (fused (graph core1397) (root 9) 2 0) DegreeTwoThreeSpectrum1995.graph fusedMap1397swap=true := by decide +kernel
theorem certified1397swap : Certified (graph core1397) (root 9) 2 0 :=
  of_native_maps core1397 DegreeTwoThreeSpectrum2269.graph DegreeTwoThreeSpectrum1995.graph
    sourceMap1397swap fusedMap1397swap sourceMap1397swap_checked fusedMap1397swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1397
#print axioms sourceMap1397swap_checked
#print axioms fusedMap1397swap_checked
#print axioms certified1397swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
