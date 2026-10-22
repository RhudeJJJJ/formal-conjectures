/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2651 : Family 10 := level10.get ⟨676,by decide⟩
def sourceMap2651 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,16,7,8,9,10,11] (sourceLabel 10 0 4 v)
def fusedMap2651 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2651_checked : acceptsGraphIso
    (source (graph core2651) (root 10) 0 4) DegreeTwoThreeSpectrum6465.graph sourceMap2651=true := by decide +kernel
theorem fusedMap2651_checked : acceptsGraphIso
    (fused (graph core2651) (root 10) 0 4) DegreeTwoThreeSpectrum5398.graph fusedMap2651=true := by decide +kernel
theorem certified2651 : Certified (graph core2651) (root 10) 0 4 :=
  of_native_maps core2651 DegreeTwoThreeSpectrum6465.graph DegreeTwoThreeSpectrum5398.graph
    sourceMap2651 fusedMap2651 sourceMap2651_checked fusedMap2651_checked
    DegreeTwoThreeFiniteComparisons.comparison2651
#print axioms sourceMap2651_checked
#print axioms fusedMap2651_checked
#print axioms certified2651
def sourceMap2651swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11,16] (sourceLabel 10 4 0 v)
def fusedMap2651swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2651swap_checked : acceptsGraphIso
    (source (graph core2651) (root 10) 4 0) DegreeTwoThreeSpectrum6465.graph sourceMap2651swap=true := by decide +kernel
theorem fusedMap2651swap_checked : acceptsGraphIso
    (fused (graph core2651) (root 10) 4 0) DegreeTwoThreeSpectrum5398.graph fusedMap2651swap=true := by decide +kernel
theorem certified2651swap : Certified (graph core2651) (root 10) 4 0 :=
  of_native_maps core2651 DegreeTwoThreeSpectrum6465.graph DegreeTwoThreeSpectrum5398.graph
    sourceMap2651swap fusedMap2651swap sourceMap2651swap_checked fusedMap2651swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2651
#print axioms sourceMap2651swap_checked
#print axioms fusedMap2651swap_checked
#print axioms certified2651swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
