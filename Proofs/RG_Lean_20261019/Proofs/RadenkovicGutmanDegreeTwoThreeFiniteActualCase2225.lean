/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2225 : Family 9 := level9.get ⟨59,by decide⟩
def sourceMap2225 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2225 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2225_checked : acceptsGraphIso
    (source (graph core2225) (root 9) 0 4) DegreeTwoThreeSpectrum3957.graph sourceMap2225=true := by decide +kernel
theorem fusedMap2225_checked : acceptsGraphIso
    (fused (graph core2225) (root 9) 0 4) DegreeTwoThreeSpectrum3958.graph fusedMap2225=true := by decide +kernel
theorem certified2225 : Certified (graph core2225) (root 9) 0 4 :=
  of_native_maps core2225 DegreeTwoThreeSpectrum3957.graph DegreeTwoThreeSpectrum3958.graph
    sourceMap2225 fusedMap2225 sourceMap2225_checked fusedMap2225_checked
    DegreeTwoThreeFiniteComparisons.comparison2225
#print axioms sourceMap2225_checked
#print axioms fusedMap2225_checked
#print axioms certified2225
def sourceMap2225swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2225swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2225swap_checked : acceptsGraphIso
    (source (graph core2225) (root 9) 4 0) DegreeTwoThreeSpectrum3957.graph sourceMap2225swap=true := by decide +kernel
theorem fusedMap2225swap_checked : acceptsGraphIso
    (fused (graph core2225) (root 9) 4 0) DegreeTwoThreeSpectrum3958.graph fusedMap2225swap=true := by decide +kernel
theorem certified2225swap : Certified (graph core2225) (root 9) 4 0 :=
  of_native_maps core2225 DegreeTwoThreeSpectrum3957.graph DegreeTwoThreeSpectrum3958.graph
    sourceMap2225swap fusedMap2225swap sourceMap2225swap_checked fusedMap2225swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2225
#print axioms sourceMap2225swap_checked
#print axioms fusedMap2225swap_checked
#print axioms certified2225swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
