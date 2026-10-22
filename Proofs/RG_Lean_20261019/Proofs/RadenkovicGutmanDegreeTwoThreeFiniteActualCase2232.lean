/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2232 : Family 9 := level9.get ⟨87,by decide⟩
def sourceMap2232 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2232 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2232_checked : acceptsGraphIso
    (source (graph core2232) (root 9) 0 4) DegreeTwoThreeSpectrum4046.graph sourceMap2232=true := by decide +kernel
theorem fusedMap2232_checked : acceptsGraphIso
    (fused (graph core2232) (root 9) 0 4) DegreeTwoThreeSpectrum4047.graph fusedMap2232=true := by decide +kernel
theorem certified2232 : Certified (graph core2232) (root 9) 0 4 :=
  of_native_maps core2232 DegreeTwoThreeSpectrum4046.graph DegreeTwoThreeSpectrum4047.graph
    sourceMap2232 fusedMap2232 sourceMap2232_checked fusedMap2232_checked
    DegreeTwoThreeFiniteComparisons.comparison2232
#print axioms sourceMap2232_checked
#print axioms fusedMap2232_checked
#print axioms certified2232
def sourceMap2232swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2232swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2232swap_checked : acceptsGraphIso
    (source (graph core2232) (root 9) 4 0) DegreeTwoThreeSpectrum4046.graph sourceMap2232swap=true := by decide +kernel
theorem fusedMap2232swap_checked : acceptsGraphIso
    (fused (graph core2232) (root 9) 4 0) DegreeTwoThreeSpectrum4047.graph fusedMap2232swap=true := by decide +kernel
theorem certified2232swap : Certified (graph core2232) (root 9) 4 0 :=
  of_native_maps core2232 DegreeTwoThreeSpectrum4046.graph DegreeTwoThreeSpectrum4047.graph
    sourceMap2232swap fusedMap2232swap sourceMap2232swap_checked fusedMap2232swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2232
#print axioms sourceMap2232swap_checked
#print axioms fusedMap2232swap_checked
#print axioms certified2232swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
