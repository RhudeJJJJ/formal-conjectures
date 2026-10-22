/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2402 : Family 9 := level9.get ⟨552,by decide⟩
def sourceMap2402 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2402 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2402_checked : acceptsGraphIso
    (source (graph core2402) (root 9) 0 4) DegreeTwoThreeSpectrum4682.graph sourceMap2402=true := by decide +kernel
theorem fusedMap2402_checked : acceptsGraphIso
    (fused (graph core2402) (root 9) 0 4) DegreeTwoThreeSpectrum4184.graph fusedMap2402=true := by decide +kernel
theorem certified2402 : Certified (graph core2402) (root 9) 0 4 :=
  of_native_maps core2402 DegreeTwoThreeSpectrum4682.graph DegreeTwoThreeSpectrum4184.graph
    sourceMap2402 fusedMap2402 sourceMap2402_checked fusedMap2402_checked
    DegreeTwoThreeFiniteComparisons.comparison2402
#print axioms sourceMap2402_checked
#print axioms fusedMap2402_checked
#print axioms certified2402
def sourceMap2402swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2402swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2402swap_checked : acceptsGraphIso
    (source (graph core2402) (root 9) 4 0) DegreeTwoThreeSpectrum4682.graph sourceMap2402swap=true := by decide +kernel
theorem fusedMap2402swap_checked : acceptsGraphIso
    (fused (graph core2402) (root 9) 4 0) DegreeTwoThreeSpectrum4184.graph fusedMap2402swap=true := by decide +kernel
theorem certified2402swap : Certified (graph core2402) (root 9) 4 0 :=
  of_native_maps core2402 DegreeTwoThreeSpectrum4682.graph DegreeTwoThreeSpectrum4184.graph
    sourceMap2402swap fusedMap2402swap sourceMap2402swap_checked fusedMap2402swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2402
#print axioms sourceMap2402swap_checked
#print axioms fusedMap2402swap_checked
#print axioms certified2402swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
