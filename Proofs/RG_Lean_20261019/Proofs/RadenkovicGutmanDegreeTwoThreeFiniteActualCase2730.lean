/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2730 : Family 10 := level10.get ⟨902,by decide⟩
def sourceMap2730 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2730 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2730_checked : acceptsGraphIso
    (source (graph core2730) (root 10) 0 4) DegreeTwoThreeSpectrum6980.graph sourceMap2730=true := by decide +kernel
theorem fusedMap2730_checked : acceptsGraphIso
    (fused (graph core2730) (root 10) 0 4) DegreeTwoThreeSpectrum5768.graph fusedMap2730=true := by decide +kernel
theorem certified2730 : Certified (graph core2730) (root 10) 0 4 :=
  of_native_maps core2730 DegreeTwoThreeSpectrum6980.graph DegreeTwoThreeSpectrum5768.graph
    sourceMap2730 fusedMap2730 sourceMap2730_checked fusedMap2730_checked
    DegreeTwoThreeFiniteComparisons.comparison2730
#print axioms sourceMap2730_checked
#print axioms fusedMap2730_checked
#print axioms certified2730
def sourceMap2730swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2730swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2730swap_checked : acceptsGraphIso
    (source (graph core2730) (root 10) 4 0) DegreeTwoThreeSpectrum6980.graph sourceMap2730swap=true := by decide +kernel
theorem fusedMap2730swap_checked : acceptsGraphIso
    (fused (graph core2730) (root 10) 4 0) DegreeTwoThreeSpectrum5768.graph fusedMap2730swap=true := by decide +kernel
theorem certified2730swap : Certified (graph core2730) (root 10) 4 0 :=
  of_native_maps core2730 DegreeTwoThreeSpectrum6980.graph DegreeTwoThreeSpectrum5768.graph
    sourceMap2730swap fusedMap2730swap sourceMap2730swap_checked fusedMap2730swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2730
#print axioms sourceMap2730swap_checked
#print axioms fusedMap2730swap_checked
#print axioms certified2730swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
