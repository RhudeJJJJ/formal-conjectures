/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2629 : Family 10 := level10.get ⟨623,by decide⟩
def sourceMap2629 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2629 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2629_checked : acceptsGraphIso
    (source (graph core2629) (root 10) 0 4) DegreeTwoThreeSpectrum6367.graph sourceMap2629=true := by decide +kernel
theorem fusedMap2629_checked : acceptsGraphIso
    (fused (graph core2629) (root 10) 0 4) DegreeTwoThreeSpectrum5314.graph fusedMap2629=true := by decide +kernel
theorem certified2629 : Certified (graph core2629) (root 10) 0 4 :=
  of_native_maps core2629 DegreeTwoThreeSpectrum6367.graph DegreeTwoThreeSpectrum5314.graph
    sourceMap2629 fusedMap2629 sourceMap2629_checked fusedMap2629_checked
    DegreeTwoThreeFiniteComparisons.comparison2629
#print axioms sourceMap2629_checked
#print axioms fusedMap2629_checked
#print axioms certified2629
def sourceMap2629swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2629swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2629swap_checked : acceptsGraphIso
    (source (graph core2629) (root 10) 4 0) DegreeTwoThreeSpectrum6367.graph sourceMap2629swap=true := by decide +kernel
theorem fusedMap2629swap_checked : acceptsGraphIso
    (fused (graph core2629) (root 10) 4 0) DegreeTwoThreeSpectrum5314.graph fusedMap2629swap=true := by decide +kernel
theorem certified2629swap : Certified (graph core2629) (root 10) 4 0 :=
  of_native_maps core2629 DegreeTwoThreeSpectrum6367.graph DegreeTwoThreeSpectrum5314.graph
    sourceMap2629swap fusedMap2629swap sourceMap2629swap_checked fusedMap2629swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2629
#print axioms sourceMap2629swap_checked
#print axioms fusedMap2629swap_checked
#print axioms certified2629swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
