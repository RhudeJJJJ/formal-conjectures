/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3949 : Family 6 := level6.get ⟨41,by decide⟩
def sourceMap3949 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 6) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14] (sourceLabel 6 1 5 v)
def fusedMap3949 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (fusedLabel 6 1 5 v)
theorem sourceMap3949_checked : acceptsGraphIso
    (source (graph core3949) (root 6) 1 5) DegreeTwoThreeSpectrum3158.graph sourceMap3949=true := by decide +kernel
theorem fusedMap3949_checked : acceptsGraphIso
    (fused (graph core3949) (root 6) 1 5) DegreeTwoThreeSpectrum2505.graph fusedMap3949=true := by decide +kernel
theorem certified3949 : Certified (graph core3949) (root 6) 1 5 :=
  of_native_maps core3949 DegreeTwoThreeSpectrum3158.graph DegreeTwoThreeSpectrum2505.graph
    sourceMap3949 fusedMap3949 sourceMap3949_checked fusedMap3949_checked
    DegreeTwoThreeFiniteComparisons.comparison3949
#print axioms sourceMap3949_checked
#print axioms fusedMap3949_checked
#print axioms certified3949
def sourceMap3949swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 2) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,11,12,13,14,9,10] (sourceLabel 6 5 1 v)
def fusedMap3949swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (fusedLabel 6 5 1 v)
theorem sourceMap3949swap_checked : acceptsGraphIso
    (source (graph core3949) (root 6) 5 1) DegreeTwoThreeSpectrum3158.graph sourceMap3949swap=true := by decide +kernel
theorem fusedMap3949swap_checked : acceptsGraphIso
    (fused (graph core3949) (root 6) 5 1) DegreeTwoThreeSpectrum2505.graph fusedMap3949swap=true := by decide +kernel
theorem certified3949swap : Certified (graph core3949) (root 6) 5 1 :=
  of_native_maps core3949 DegreeTwoThreeSpectrum3158.graph DegreeTwoThreeSpectrum2505.graph
    sourceMap3949swap fusedMap3949swap sourceMap3949swap_checked fusedMap3949swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3949
#print axioms sourceMap3949swap_checked
#print axioms fusedMap3949swap_checked
#print axioms certified3949swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
