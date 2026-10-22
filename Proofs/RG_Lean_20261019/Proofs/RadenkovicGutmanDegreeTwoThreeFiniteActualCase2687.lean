/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2687 : Family 10 := level10.get ⟨786,by decide⟩
def sourceMap2687 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2687 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2687_checked : acceptsGraphIso
    (source (graph core2687) (root 10) 0 4) DegreeTwoThreeSpectrum6726.graph sourceMap2687=true := by decide +kernel
theorem fusedMap2687_checked : acceptsGraphIso
    (fused (graph core2687) (root 10) 0 4) DegreeTwoThreeSpectrum5568.graph fusedMap2687=true := by decide +kernel
theorem certified2687 : Certified (graph core2687) (root 10) 0 4 :=
  of_native_maps core2687 DegreeTwoThreeSpectrum6726.graph DegreeTwoThreeSpectrum5568.graph
    sourceMap2687 fusedMap2687 sourceMap2687_checked fusedMap2687_checked
    DegreeTwoThreeFiniteComparisons.comparison2687
#print axioms sourceMap2687_checked
#print axioms fusedMap2687_checked
#print axioms certified2687
def sourceMap2687swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2687swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2687swap_checked : acceptsGraphIso
    (source (graph core2687) (root 10) 4 0) DegreeTwoThreeSpectrum6726.graph sourceMap2687swap=true := by decide +kernel
theorem fusedMap2687swap_checked : acceptsGraphIso
    (fused (graph core2687) (root 10) 4 0) DegreeTwoThreeSpectrum5568.graph fusedMap2687swap=true := by decide +kernel
theorem certified2687swap : Certified (graph core2687) (root 10) 4 0 :=
  of_native_maps core2687 DegreeTwoThreeSpectrum6726.graph DegreeTwoThreeSpectrum5568.graph
    sourceMap2687swap fusedMap2687swap sourceMap2687swap_checked fusedMap2687swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2687
#print axioms sourceMap2687swap_checked
#print axioms fusedMap2687swap_checked
#print axioms certified2687swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
