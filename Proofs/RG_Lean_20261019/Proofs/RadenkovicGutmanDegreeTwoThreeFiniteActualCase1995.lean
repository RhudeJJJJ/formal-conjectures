/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1995 : Family 10 := level10.get ⟨1607,by decide⟩
def sourceMap1995 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,14,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1995 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1995_checked : acceptsGraphIso
    (source (graph core1995) (root 10) 0 2) DegreeTwoThreeSpectrum3782.graph sourceMap1995=true := by decide +kernel
theorem fusedMap1995_checked : acceptsGraphIso
    (fused (graph core1995) (root 10) 0 2) DegreeTwoThreeSpectrum3122.graph fusedMap1995=true := by decide +kernel
theorem certified1995 : Certified (graph core1995) (root 10) 0 2 :=
  of_native_maps core1995 DegreeTwoThreeSpectrum3782.graph DegreeTwoThreeSpectrum3122.graph
    sourceMap1995 fusedMap1995 sourceMap1995_checked fusedMap1995_checked
    DegreeTwoThreeFiniteComparisons.comparison1995
#print axioms sourceMap1995_checked
#print axioms fusedMap1995_checked
#print axioms certified1995
def sourceMap1995swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,6,7,8,14] (sourceLabel 10 2 0 v)
def fusedMap1995swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1995swap_checked : acceptsGraphIso
    (source (graph core1995) (root 10) 2 0) DegreeTwoThreeSpectrum3782.graph sourceMap1995swap=true := by decide +kernel
theorem fusedMap1995swap_checked : acceptsGraphIso
    (fused (graph core1995) (root 10) 2 0) DegreeTwoThreeSpectrum3122.graph fusedMap1995swap=true := by decide +kernel
theorem certified1995swap : Certified (graph core1995) (root 10) 2 0 :=
  of_native_maps core1995 DegreeTwoThreeSpectrum3782.graph DegreeTwoThreeSpectrum3122.graph
    sourceMap1995swap fusedMap1995swap sourceMap1995swap_checked fusedMap1995swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1995
#print axioms sourceMap1995swap_checked
#print axioms fusedMap1995swap_checked
#print axioms certified1995swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
