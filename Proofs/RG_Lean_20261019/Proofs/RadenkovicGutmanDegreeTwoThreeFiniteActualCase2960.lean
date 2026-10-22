/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2960 : Family 10 := level10.get ⟨1459,by decide⟩
def sourceMap2960 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2960 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2960_checked : acceptsGraphIso
    (source (graph core2960) (root 10) 0 4) DegreeTwoThreeSpectrum6931.graph sourceMap2960=true := by decide +kernel
theorem fusedMap2960_checked : acceptsGraphIso
    (fused (graph core2960) (root 10) 0 4) DegreeTwoThreeSpectrum6932.graph fusedMap2960=true := by decide +kernel
theorem certified2960 : Certified (graph core2960) (root 10) 0 4 :=
  of_native_maps core2960 DegreeTwoThreeSpectrum6931.graph DegreeTwoThreeSpectrum6932.graph
    sourceMap2960 fusedMap2960 sourceMap2960_checked fusedMap2960_checked
    DegreeTwoThreeFiniteComparisons.comparison2960
#print axioms sourceMap2960_checked
#print axioms fusedMap2960_checked
#print axioms certified2960
def sourceMap2960swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2960swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2960swap_checked : acceptsGraphIso
    (source (graph core2960) (root 10) 4 0) DegreeTwoThreeSpectrum6931.graph sourceMap2960swap=true := by decide +kernel
theorem fusedMap2960swap_checked : acceptsGraphIso
    (fused (graph core2960) (root 10) 4 0) DegreeTwoThreeSpectrum6932.graph fusedMap2960swap=true := by decide +kernel
theorem certified2960swap : Certified (graph core2960) (root 10) 4 0 :=
  of_native_maps core2960 DegreeTwoThreeSpectrum6931.graph DegreeTwoThreeSpectrum6932.graph
    sourceMap2960swap fusedMap2960swap sourceMap2960swap_checked fusedMap2960swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2960
#print axioms sourceMap2960swap_checked
#print axioms fusedMap2960swap_checked
#print axioms certified2960swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
