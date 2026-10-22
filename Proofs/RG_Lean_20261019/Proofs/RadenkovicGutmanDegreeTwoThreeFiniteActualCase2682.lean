/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2682 : Family 10 := level10.get ⟨774,by decide⟩
def sourceMap2682 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2682 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2682_checked : acceptsGraphIso
    (source (graph core2682) (root 10) 0 4) DegreeTwoThreeSpectrum6704.graph sourceMap2682=true := by decide +kernel
theorem fusedMap2682_checked : acceptsGraphIso
    (fused (graph core2682) (root 10) 0 4) DegreeTwoThreeSpectrum5551.graph fusedMap2682=true := by decide +kernel
theorem certified2682 : Certified (graph core2682) (root 10) 0 4 :=
  of_native_maps core2682 DegreeTwoThreeSpectrum6704.graph DegreeTwoThreeSpectrum5551.graph
    sourceMap2682 fusedMap2682 sourceMap2682_checked fusedMap2682_checked
    DegreeTwoThreeFiniteComparisons.comparison2682
#print axioms sourceMap2682_checked
#print axioms fusedMap2682_checked
#print axioms certified2682
def sourceMap2682swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2682swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2682swap_checked : acceptsGraphIso
    (source (graph core2682) (root 10) 4 0) DegreeTwoThreeSpectrum6704.graph sourceMap2682swap=true := by decide +kernel
theorem fusedMap2682swap_checked : acceptsGraphIso
    (fused (graph core2682) (root 10) 4 0) DegreeTwoThreeSpectrum5551.graph fusedMap2682swap=true := by decide +kernel
theorem certified2682swap : Certified (graph core2682) (root 10) 4 0 :=
  of_native_maps core2682 DegreeTwoThreeSpectrum6704.graph DegreeTwoThreeSpectrum5551.graph
    sourceMap2682swap fusedMap2682swap sourceMap2682swap_checked fusedMap2682swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2682
#print axioms sourceMap2682swap_checked
#print axioms fusedMap2682swap_checked
#print axioms certified2682swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
