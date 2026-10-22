/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2652 : Family 10 := level10.get ⟨678,by decide⟩
def sourceMap2652 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,16,7,8,9,10,11] (sourceLabel 10 0 4 v)
def fusedMap2652 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2652_checked : acceptsGraphIso
    (source (graph core2652) (root 10) 0 4) DegreeTwoThreeSpectrum6467.graph sourceMap2652=true := by decide +kernel
theorem fusedMap2652_checked : acceptsGraphIso
    (fused (graph core2652) (root 10) 0 4) DegreeTwoThreeSpectrum5401.graph fusedMap2652=true := by decide +kernel
theorem certified2652 : Certified (graph core2652) (root 10) 0 4 :=
  of_native_maps core2652 DegreeTwoThreeSpectrum6467.graph DegreeTwoThreeSpectrum5401.graph
    sourceMap2652 fusedMap2652 sourceMap2652_checked fusedMap2652_checked
    DegreeTwoThreeFiniteComparisons.comparison2652
#print axioms sourceMap2652_checked
#print axioms fusedMap2652_checked
#print axioms certified2652
def sourceMap2652swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11,16] (sourceLabel 10 4 0 v)
def fusedMap2652swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2652swap_checked : acceptsGraphIso
    (source (graph core2652) (root 10) 4 0) DegreeTwoThreeSpectrum6467.graph sourceMap2652swap=true := by decide +kernel
theorem fusedMap2652swap_checked : acceptsGraphIso
    (fused (graph core2652) (root 10) 4 0) DegreeTwoThreeSpectrum5401.graph fusedMap2652swap=true := by decide +kernel
theorem certified2652swap : Certified (graph core2652) (root 10) 4 0 :=
  of_native_maps core2652 DegreeTwoThreeSpectrum6467.graph DegreeTwoThreeSpectrum5401.graph
    sourceMap2652swap fusedMap2652swap sourceMap2652swap_checked fusedMap2652swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2652
#print axioms sourceMap2652swap_checked
#print axioms fusedMap2652swap_checked
#print axioms certified2652swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
