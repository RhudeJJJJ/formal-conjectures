/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2223 : Family 9 := level9.get ⟨48,by decide⟩
def sourceMap2223 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2223 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2223_checked : acceptsGraphIso
    (source (graph core2223) (root 9) 0 4) DegreeTwoThreeSpectrum3915.graph sourceMap2223=true := by decide +kernel
theorem fusedMap2223_checked : acceptsGraphIso
    (fused (graph core2223) (root 9) 0 4) DegreeTwoThreeSpectrum3916.graph fusedMap2223=true := by decide +kernel
theorem certified2223 : Certified (graph core2223) (root 9) 0 4 :=
  of_native_maps core2223 DegreeTwoThreeSpectrum3915.graph DegreeTwoThreeSpectrum3916.graph
    sourceMap2223 fusedMap2223 sourceMap2223_checked fusedMap2223_checked
    DegreeTwoThreeFiniteComparisons.comparison2223
#print axioms sourceMap2223_checked
#print axioms fusedMap2223_checked
#print axioms certified2223
def sourceMap2223swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2223swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2223swap_checked : acceptsGraphIso
    (source (graph core2223) (root 9) 4 0) DegreeTwoThreeSpectrum3915.graph sourceMap2223swap=true := by decide +kernel
theorem fusedMap2223swap_checked : acceptsGraphIso
    (fused (graph core2223) (root 9) 4 0) DegreeTwoThreeSpectrum3916.graph fusedMap2223swap=true := by decide +kernel
theorem certified2223swap : Certified (graph core2223) (root 9) 4 0 :=
  of_native_maps core2223 DegreeTwoThreeSpectrum3915.graph DegreeTwoThreeSpectrum3916.graph
    sourceMap2223swap fusedMap2223swap sourceMap2223swap_checked fusedMap2223swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2223
#print axioms sourceMap2223swap_checked
#print axioms fusedMap2223swap_checked
#print axioms certified2223swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
