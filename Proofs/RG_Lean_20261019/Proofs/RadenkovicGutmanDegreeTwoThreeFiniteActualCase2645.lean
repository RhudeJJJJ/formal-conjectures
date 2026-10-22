/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2645 : Family 10 := level10.get ⟨667,by decide⟩
def sourceMap2645 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2645 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2645_checked : acceptsGraphIso
    (source (graph core2645) (root 10) 0 4) DegreeTwoThreeSpectrum6446.graph sourceMap2645=true := by decide +kernel
theorem fusedMap2645_checked : acceptsGraphIso
    (fused (graph core2645) (root 10) 0 4) DegreeTwoThreeSpectrum5379.graph fusedMap2645=true := by decide +kernel
theorem certified2645 : Certified (graph core2645) (root 10) 0 4 :=
  of_native_maps core2645 DegreeTwoThreeSpectrum6446.graph DegreeTwoThreeSpectrum5379.graph
    sourceMap2645 fusedMap2645 sourceMap2645_checked fusedMap2645_checked
    DegreeTwoThreeFiniteComparisons.comparison2645
#print axioms sourceMap2645_checked
#print axioms fusedMap2645_checked
#print axioms certified2645
def sourceMap2645swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2645swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2645swap_checked : acceptsGraphIso
    (source (graph core2645) (root 10) 4 0) DegreeTwoThreeSpectrum6446.graph sourceMap2645swap=true := by decide +kernel
theorem fusedMap2645swap_checked : acceptsGraphIso
    (fused (graph core2645) (root 10) 4 0) DegreeTwoThreeSpectrum5379.graph fusedMap2645swap=true := by decide +kernel
theorem certified2645swap : Certified (graph core2645) (root 10) 4 0 :=
  of_native_maps core2645 DegreeTwoThreeSpectrum6446.graph DegreeTwoThreeSpectrum5379.graph
    sourceMap2645swap fusedMap2645swap sourceMap2645swap_checked fusedMap2645swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2645
#print axioms sourceMap2645swap_checked
#print axioms fusedMap2645swap_checked
#print axioms certified2645swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
