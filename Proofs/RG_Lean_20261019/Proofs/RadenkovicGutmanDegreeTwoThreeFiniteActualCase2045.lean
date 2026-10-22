/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2045 : Family 10 := level10.get ⟨1755,by decide⟩
def sourceMap2045 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,14,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap2045 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2045_checked : acceptsGraphIso
    (source (graph core2045) (root 10) 0 2) DegreeTwoThreeSpectrum3845.graph sourceMap2045=true := by decide +kernel
theorem fusedMap2045_checked : acceptsGraphIso
    (fused (graph core2045) (root 10) 0 2) DegreeTwoThreeSpectrum3494.graph fusedMap2045=true := by decide +kernel
theorem certified2045 : Certified (graph core2045) (root 10) 0 2 :=
  of_native_maps core2045 DegreeTwoThreeSpectrum3845.graph DegreeTwoThreeSpectrum3494.graph
    sourceMap2045 fusedMap2045 sourceMap2045_checked fusedMap2045_checked
    DegreeTwoThreeFiniteComparisons.comparison2045
#print axioms sourceMap2045_checked
#print axioms fusedMap2045_checked
#print axioms certified2045
def sourceMap2045swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,6,7,8,14] (sourceLabel 10 2 0 v)
def fusedMap2045swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2045swap_checked : acceptsGraphIso
    (source (graph core2045) (root 10) 2 0) DegreeTwoThreeSpectrum3845.graph sourceMap2045swap=true := by decide +kernel
theorem fusedMap2045swap_checked : acceptsGraphIso
    (fused (graph core2045) (root 10) 2 0) DegreeTwoThreeSpectrum3494.graph fusedMap2045swap=true := by decide +kernel
theorem certified2045swap : Certified (graph core2045) (root 10) 2 0 :=
  of_native_maps core2045 DegreeTwoThreeSpectrum3845.graph DegreeTwoThreeSpectrum3494.graph
    sourceMap2045swap fusedMap2045swap sourceMap2045swap_checked fusedMap2045swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2045
#print axioms sourceMap2045swap_checked
#print axioms fusedMap2045swap_checked
#print axioms certified2045swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
