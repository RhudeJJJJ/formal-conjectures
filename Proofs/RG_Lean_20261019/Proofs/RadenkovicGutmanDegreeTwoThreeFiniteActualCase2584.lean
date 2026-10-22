/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2584 : Family 10 := level10.get ⟨482,by decide⟩
def sourceMap2584 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,9,10,11,12,13,14,15,16,6,7,8,1,2,3,4,5] (sourceLabel 10 0 4 v)
def fusedMap2584 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2584_checked : acceptsGraphIso
    (source (graph core2584) (root 10) 0 4) DegreeTwoThreeSpectrum5938.graph sourceMap2584=true := by decide +kernel
theorem fusedMap2584_checked : acceptsGraphIso
    (fused (graph core2584) (root 10) 0 4) DegreeTwoThreeSpectrum5948.graph fusedMap2584=true := by decide +kernel
theorem certified2584 : Certified (graph core2584) (root 10) 0 4 :=
  of_native_maps core2584 DegreeTwoThreeSpectrum5938.graph DegreeTwoThreeSpectrum5948.graph
    sourceMap2584 fusedMap2584 sourceMap2584_checked fusedMap2584_checked
    DegreeTwoThreeFiniteComparisons.comparison2584
#print axioms sourceMap2584_checked
#print axioms fusedMap2584_checked
#print axioms certified2584
def sourceMap2584swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,9,10,11,12,13,14,15,16,6,7,1,2,3,4,5,8] (sourceLabel 10 4 0 v)
def fusedMap2584swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2584swap_checked : acceptsGraphIso
    (source (graph core2584) (root 10) 4 0) DegreeTwoThreeSpectrum5938.graph sourceMap2584swap=true := by decide +kernel
theorem fusedMap2584swap_checked : acceptsGraphIso
    (fused (graph core2584) (root 10) 4 0) DegreeTwoThreeSpectrum5948.graph fusedMap2584swap=true := by decide +kernel
theorem certified2584swap : Certified (graph core2584) (root 10) 4 0 :=
  of_native_maps core2584 DegreeTwoThreeSpectrum5938.graph DegreeTwoThreeSpectrum5948.graph
    sourceMap2584swap fusedMap2584swap sourceMap2584swap_checked fusedMap2584swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2584
#print axioms sourceMap2584swap_checked
#print axioms fusedMap2584swap_checked
#print axioms certified2584swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
