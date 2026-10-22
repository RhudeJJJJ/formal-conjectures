/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3402 : Family 9 := level9.get ⟨500,by decide⟩
def sourceMap3402 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3402 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3402_checked : acceptsGraphIso
    (source (graph core3402) (root 9) 0 5) DegreeTwoThreeSpectrum6900.graph sourceMap3402=true := by decide +kernel
theorem fusedMap3402_checked : acceptsGraphIso
    (fused (graph core3402) (root 9) 0 5) DegreeTwoThreeSpectrum5689.graph fusedMap3402=true := by decide +kernel
theorem certified3402 : Certified (graph core3402) (root 9) 0 5 :=
  of_native_maps core3402 DegreeTwoThreeSpectrum6900.graph DegreeTwoThreeSpectrum5689.graph
    sourceMap3402 fusedMap3402 sourceMap3402_checked fusedMap3402_checked
    DegreeTwoThreeFiniteComparisons.comparison3402
#print axioms sourceMap3402_checked
#print axioms fusedMap3402_checked
#print axioms certified3402
def sourceMap3402swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3402swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3402swap_checked : acceptsGraphIso
    (source (graph core3402) (root 9) 5 0) DegreeTwoThreeSpectrum6900.graph sourceMap3402swap=true := by decide +kernel
theorem fusedMap3402swap_checked : acceptsGraphIso
    (fused (graph core3402) (root 9) 5 0) DegreeTwoThreeSpectrum5689.graph fusedMap3402swap=true := by decide +kernel
theorem certified3402swap : Certified (graph core3402) (root 9) 5 0 :=
  of_native_maps core3402 DegreeTwoThreeSpectrum6900.graph DegreeTwoThreeSpectrum5689.graph
    sourceMap3402swap fusedMap3402swap sourceMap3402swap_checked fusedMap3402swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3402
#print axioms sourceMap3402swap_checked
#print axioms fusedMap3402swap_checked
#print axioms certified3402swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
