/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2683 : Family 10 := level10.get ⟨777,by decide⟩
def sourceMap2683 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2683 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2683_checked : acceptsGraphIso
    (source (graph core2683) (root 10) 0 4) DegreeTwoThreeSpectrum6710.graph sourceMap2683=true := by decide +kernel
theorem fusedMap2683_checked : acceptsGraphIso
    (fused (graph core2683) (root 10) 0 4) DegreeTwoThreeSpectrum5555.graph fusedMap2683=true := by decide +kernel
theorem certified2683 : Certified (graph core2683) (root 10) 0 4 :=
  of_native_maps core2683 DegreeTwoThreeSpectrum6710.graph DegreeTwoThreeSpectrum5555.graph
    sourceMap2683 fusedMap2683 sourceMap2683_checked fusedMap2683_checked
    DegreeTwoThreeFiniteComparisons.comparison2683
#print axioms sourceMap2683_checked
#print axioms fusedMap2683_checked
#print axioms certified2683
def sourceMap2683swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2683swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2683swap_checked : acceptsGraphIso
    (source (graph core2683) (root 10) 4 0) DegreeTwoThreeSpectrum6710.graph sourceMap2683swap=true := by decide +kernel
theorem fusedMap2683swap_checked : acceptsGraphIso
    (fused (graph core2683) (root 10) 4 0) DegreeTwoThreeSpectrum5555.graph fusedMap2683swap=true := by decide +kernel
theorem certified2683swap : Certified (graph core2683) (root 10) 4 0 :=
  of_native_maps core2683 DegreeTwoThreeSpectrum6710.graph DegreeTwoThreeSpectrum5555.graph
    sourceMap2683swap fusedMap2683swap sourceMap2683swap_checked fusedMap2683swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2683
#print axioms sourceMap2683swap_checked
#print axioms fusedMap2683swap_checked
#print axioms certified2683swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
