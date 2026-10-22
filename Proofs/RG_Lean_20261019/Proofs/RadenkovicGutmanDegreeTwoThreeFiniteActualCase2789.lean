/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2789 : Family 10 := level10.get ⟨1050,by decide⟩
def sourceMap2789 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2789 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2789_checked : acceptsGraphIso
    (source (graph core2789) (root 10) 0 4) DegreeTwoThreeSpectrum6084.graph sourceMap2789=true := by decide +kernel
theorem fusedMap2789_checked : acceptsGraphIso
    (fused (graph core2789) (root 10) 0 4) DegreeTwoThreeSpectrum6085.graph fusedMap2789=true := by decide +kernel
theorem certified2789 : Certified (graph core2789) (root 10) 0 4 :=
  of_native_maps core2789 DegreeTwoThreeSpectrum6084.graph DegreeTwoThreeSpectrum6085.graph
    sourceMap2789 fusedMap2789 sourceMap2789_checked fusedMap2789_checked
    DegreeTwoThreeFiniteComparisons.comparison2789
#print axioms sourceMap2789_checked
#print axioms fusedMap2789_checked
#print axioms certified2789
def sourceMap2789swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2789swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2789swap_checked : acceptsGraphIso
    (source (graph core2789) (root 10) 4 0) DegreeTwoThreeSpectrum6084.graph sourceMap2789swap=true := by decide +kernel
theorem fusedMap2789swap_checked : acceptsGraphIso
    (fused (graph core2789) (root 10) 4 0) DegreeTwoThreeSpectrum6085.graph fusedMap2789swap=true := by decide +kernel
theorem certified2789swap : Certified (graph core2789) (root 10) 4 0 :=
  of_native_maps core2789 DegreeTwoThreeSpectrum6084.graph DegreeTwoThreeSpectrum6085.graph
    sourceMap2789swap fusedMap2789swap sourceMap2789swap_checked fusedMap2789swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2789
#print axioms sourceMap2789swap_checked
#print axioms fusedMap2789swap_checked
#print axioms certified2789swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
