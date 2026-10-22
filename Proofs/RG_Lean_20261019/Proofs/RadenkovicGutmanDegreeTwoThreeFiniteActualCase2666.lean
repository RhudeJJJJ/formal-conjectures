/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2666 : Family 10 := level10.get ⟨722,by decide⟩
def sourceMap2666 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2666 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2666_checked : acceptsGraphIso
    (source (graph core2666) (root 10) 0 4) DegreeTwoThreeSpectrum6579.graph sourceMap2666=true := by decide +kernel
theorem fusedMap2666_checked : acceptsGraphIso
    (fused (graph core2666) (root 10) 0 4) DegreeTwoThreeSpectrum5472.graph fusedMap2666=true := by decide +kernel
theorem certified2666 : Certified (graph core2666) (root 10) 0 4 :=
  of_native_maps core2666 DegreeTwoThreeSpectrum6579.graph DegreeTwoThreeSpectrum5472.graph
    sourceMap2666 fusedMap2666 sourceMap2666_checked fusedMap2666_checked
    DegreeTwoThreeFiniteComparisons.comparison2666
#print axioms sourceMap2666_checked
#print axioms fusedMap2666_checked
#print axioms certified2666
def sourceMap2666swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2666swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2666swap_checked : acceptsGraphIso
    (source (graph core2666) (root 10) 4 0) DegreeTwoThreeSpectrum6579.graph sourceMap2666swap=true := by decide +kernel
theorem fusedMap2666swap_checked : acceptsGraphIso
    (fused (graph core2666) (root 10) 4 0) DegreeTwoThreeSpectrum5472.graph fusedMap2666swap=true := by decide +kernel
theorem certified2666swap : Certified (graph core2666) (root 10) 4 0 :=
  of_native_maps core2666 DegreeTwoThreeSpectrum6579.graph DegreeTwoThreeSpectrum5472.graph
    sourceMap2666swap fusedMap2666swap sourceMap2666swap_checked fusedMap2666swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2666
#print axioms sourceMap2666swap_checked
#print axioms fusedMap2666swap_checked
#print axioms certified2666swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
