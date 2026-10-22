/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3995 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap3995 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (sourceLabel 5 1 6 v)
def fusedMap3995 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 1 6 v)
theorem sourceMap3995_checked : acceptsGraphIso
    (source (graph core3995) (root 5) 1 6) DegreeTwoThreeSpectrum2842.graph sourceMap3995=true := by decide +kernel
theorem fusedMap3995_checked : acceptsGraphIso
    (fused (graph core3995) (root 5) 1 6) DegreeTwoThreeSpectrum2387.graph fusedMap3995=true := by decide +kernel
theorem certified3995 : Certified (graph core3995) (root 5) 1 6 :=
  of_native_maps core3995 DegreeTwoThreeSpectrum2842.graph DegreeTwoThreeSpectrum2387.graph
    sourceMap3995 fusedMap3995 sourceMap3995_checked fusedMap3995_checked
    DegreeTwoThreeFiniteComparisons.comparison3995
#print axioms sourceMap3995_checked
#print axioms fusedMap3995_checked
#print axioms certified3995
def sourceMap3995swap : (Vertices 5 ⊕ Fin 7 ⊕ Fin 2) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,1,0,10,11,12,13,14,8,9] (sourceLabel 5 6 1 v)
def fusedMap3995swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 6 1 v)
theorem sourceMap3995swap_checked : acceptsGraphIso
    (source (graph core3995) (root 5) 6 1) DegreeTwoThreeSpectrum2842.graph sourceMap3995swap=true := by decide +kernel
theorem fusedMap3995swap_checked : acceptsGraphIso
    (fused (graph core3995) (root 5) 6 1) DegreeTwoThreeSpectrum2387.graph fusedMap3995swap=true := by decide +kernel
theorem certified3995swap : Certified (graph core3995) (root 5) 6 1 :=
  of_native_maps core3995 DegreeTwoThreeSpectrum2842.graph DegreeTwoThreeSpectrum2387.graph
    sourceMap3995swap fusedMap3995swap sourceMap3995swap_checked fusedMap3995swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3995
#print axioms sourceMap3995swap_checked
#print axioms fusedMap3995swap_checked
#print axioms certified3995swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
