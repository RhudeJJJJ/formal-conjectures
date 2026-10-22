/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2676 : Family 10 := level10.get ⟨756,by decide⟩
def sourceMap2676 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2676 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2676_checked : acceptsGraphIso
    (source (graph core2676) (root 10) 0 4) DegreeTwoThreeSpectrum6665.graph sourceMap2676=true := by decide +kernel
theorem fusedMap2676_checked : acceptsGraphIso
    (fused (graph core2676) (root 10) 0 4) DegreeTwoThreeSpectrum5522.graph fusedMap2676=true := by decide +kernel
theorem certified2676 : Certified (graph core2676) (root 10) 0 4 :=
  of_native_maps core2676 DegreeTwoThreeSpectrum6665.graph DegreeTwoThreeSpectrum5522.graph
    sourceMap2676 fusedMap2676 sourceMap2676_checked fusedMap2676_checked
    DegreeTwoThreeFiniteComparisons.comparison2676
#print axioms sourceMap2676_checked
#print axioms fusedMap2676_checked
#print axioms certified2676
def sourceMap2676swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2676swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2676swap_checked : acceptsGraphIso
    (source (graph core2676) (root 10) 4 0) DegreeTwoThreeSpectrum6665.graph sourceMap2676swap=true := by decide +kernel
theorem fusedMap2676swap_checked : acceptsGraphIso
    (fused (graph core2676) (root 10) 4 0) DegreeTwoThreeSpectrum5522.graph fusedMap2676swap=true := by decide +kernel
theorem certified2676swap : Certified (graph core2676) (root 10) 4 0 :=
  of_native_maps core2676 DegreeTwoThreeSpectrum6665.graph DegreeTwoThreeSpectrum5522.graph
    sourceMap2676swap fusedMap2676swap sourceMap2676swap_checked fusedMap2676swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2676
#print axioms sourceMap2676swap_checked
#print axioms fusedMap2676swap_checked
#print axioms certified2676swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
