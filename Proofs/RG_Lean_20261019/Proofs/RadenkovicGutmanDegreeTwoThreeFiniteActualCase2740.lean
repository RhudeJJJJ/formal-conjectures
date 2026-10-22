/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2740 : Family 10 := level10.get ⟨920,by decide⟩
def sourceMap2740 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,16,7,8,9,10,11] (sourceLabel 10 0 4 v)
def fusedMap2740 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2740_checked : acceptsGraphIso
    (source (graph core2740) (root 10) 0 4) DegreeTwoThreeSpectrum6992.graph sourceMap2740=true := by decide +kernel
theorem fusedMap2740_checked : acceptsGraphIso
    (fused (graph core2740) (root 10) 0 4) DegreeTwoThreeSpectrum5799.graph fusedMap2740=true := by decide +kernel
theorem certified2740 : Certified (graph core2740) (root 10) 0 4 :=
  of_native_maps core2740 DegreeTwoThreeSpectrum6992.graph DegreeTwoThreeSpectrum5799.graph
    sourceMap2740 fusedMap2740 sourceMap2740_checked fusedMap2740_checked
    DegreeTwoThreeFiniteComparisons.comparison2740
#print axioms sourceMap2740_checked
#print axioms fusedMap2740_checked
#print axioms certified2740
def sourceMap2740swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11,16] (sourceLabel 10 4 0 v)
def fusedMap2740swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2740swap_checked : acceptsGraphIso
    (source (graph core2740) (root 10) 4 0) DegreeTwoThreeSpectrum6992.graph sourceMap2740swap=true := by decide +kernel
theorem fusedMap2740swap_checked : acceptsGraphIso
    (fused (graph core2740) (root 10) 4 0) DegreeTwoThreeSpectrum5799.graph fusedMap2740swap=true := by decide +kernel
theorem certified2740swap : Certified (graph core2740) (root 10) 4 0 :=
  of_native_maps core2740 DegreeTwoThreeSpectrum6992.graph DegreeTwoThreeSpectrum5799.graph
    sourceMap2740swap fusedMap2740swap sourceMap2740swap_checked fusedMap2740swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2740
#print axioms sourceMap2740swap_checked
#print axioms fusedMap2740swap_checked
#print axioms certified2740swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
