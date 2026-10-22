/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2715 : Family 10 := level10.get ⟨861,by decide⟩
def sourceMap2715 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2715 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2715_checked : acceptsGraphIso
    (source (graph core2715) (root 10) 0 4) DegreeTwoThreeSpectrum6914.graph sourceMap2715=true := by decide +kernel
theorem fusedMap2715_checked : acceptsGraphIso
    (fused (graph core2715) (root 10) 0 4) DegreeTwoThreeSpectrum5698.graph fusedMap2715=true := by decide +kernel
theorem certified2715 : Certified (graph core2715) (root 10) 0 4 :=
  of_native_maps core2715 DegreeTwoThreeSpectrum6914.graph DegreeTwoThreeSpectrum5698.graph
    sourceMap2715 fusedMap2715 sourceMap2715_checked fusedMap2715_checked
    DegreeTwoThreeFiniteComparisons.comparison2715
#print axioms sourceMap2715_checked
#print axioms fusedMap2715_checked
#print axioms certified2715
def sourceMap2715swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2715swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2715swap_checked : acceptsGraphIso
    (source (graph core2715) (root 10) 4 0) DegreeTwoThreeSpectrum6914.graph sourceMap2715swap=true := by decide +kernel
theorem fusedMap2715swap_checked : acceptsGraphIso
    (fused (graph core2715) (root 10) 4 0) DegreeTwoThreeSpectrum5698.graph fusedMap2715swap=true := by decide +kernel
theorem certified2715swap : Certified (graph core2715) (root 10) 4 0 :=
  of_native_maps core2715 DegreeTwoThreeSpectrum6914.graph DegreeTwoThreeSpectrum5698.graph
    sourceMap2715swap fusedMap2715swap sourceMap2715swap_checked fusedMap2715swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2715
#print axioms sourceMap2715swap_checked
#print axioms fusedMap2715swap_checked
#print axioms certified2715swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
