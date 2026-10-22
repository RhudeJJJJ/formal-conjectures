/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2729 : Family 10 := level10.get ⟨899,by decide⟩
def sourceMap2729 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2729 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2729_checked : acceptsGraphIso
    (source (graph core2729) (root 10) 0 4) DegreeTwoThreeSpectrum6976.graph sourceMap2729=true := by decide +kernel
theorem fusedMap2729_checked : acceptsGraphIso
    (fused (graph core2729) (root 10) 0 4) DegreeTwoThreeSpectrum5764.graph fusedMap2729=true := by decide +kernel
theorem certified2729 : Certified (graph core2729) (root 10) 0 4 :=
  of_native_maps core2729 DegreeTwoThreeSpectrum6976.graph DegreeTwoThreeSpectrum5764.graph
    sourceMap2729 fusedMap2729 sourceMap2729_checked fusedMap2729_checked
    DegreeTwoThreeFiniteComparisons.comparison2729
#print axioms sourceMap2729_checked
#print axioms fusedMap2729_checked
#print axioms certified2729
def sourceMap2729swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2729swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2729swap_checked : acceptsGraphIso
    (source (graph core2729) (root 10) 4 0) DegreeTwoThreeSpectrum6976.graph sourceMap2729swap=true := by decide +kernel
theorem fusedMap2729swap_checked : acceptsGraphIso
    (fused (graph core2729) (root 10) 4 0) DegreeTwoThreeSpectrum5764.graph fusedMap2729swap=true := by decide +kernel
theorem certified2729swap : Certified (graph core2729) (root 10) 4 0 :=
  of_native_maps core2729 DegreeTwoThreeSpectrum6976.graph DegreeTwoThreeSpectrum5764.graph
    sourceMap2729swap fusedMap2729swap sourceMap2729swap_checked fusedMap2729swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2729
#print axioms sourceMap2729swap_checked
#print axioms fusedMap2729swap_checked
#print axioms certified2729swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
