/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2593 : Family 10 := level10.get ⟨510,by decide⟩
def sourceMap2593 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2593 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2593_checked : acceptsGraphIso
    (source (graph core2593) (root 10) 0 4) DegreeTwoThreeSpectrum6036.graph sourceMap2593=true := by decide +kernel
theorem fusedMap2593_checked : acceptsGraphIso
    (fused (graph core2593) (root 10) 0 4) DegreeTwoThreeSpectrum5148.graph fusedMap2593=true := by decide +kernel
theorem certified2593 : Certified (graph core2593) (root 10) 0 4 :=
  of_native_maps core2593 DegreeTwoThreeSpectrum6036.graph DegreeTwoThreeSpectrum5148.graph
    sourceMap2593 fusedMap2593 sourceMap2593_checked fusedMap2593_checked
    DegreeTwoThreeFiniteComparisons.comparison2593
#print axioms sourceMap2593_checked
#print axioms fusedMap2593_checked
#print axioms certified2593
def sourceMap2593swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2593swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2593swap_checked : acceptsGraphIso
    (source (graph core2593) (root 10) 4 0) DegreeTwoThreeSpectrum6036.graph sourceMap2593swap=true := by decide +kernel
theorem fusedMap2593swap_checked : acceptsGraphIso
    (fused (graph core2593) (root 10) 4 0) DegreeTwoThreeSpectrum5148.graph fusedMap2593swap=true := by decide +kernel
theorem certified2593swap : Certified (graph core2593) (root 10) 4 0 :=
  of_native_maps core2593 DegreeTwoThreeSpectrum6036.graph DegreeTwoThreeSpectrum5148.graph
    sourceMap2593swap fusedMap2593swap sourceMap2593swap_checked fusedMap2593swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2593
#print axioms sourceMap2593swap_checked
#print axioms fusedMap2593swap_checked
#print axioms certified2593swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
