/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2468 : Family 10 := level10.get ⟨84,by decide⟩
def sourceMap2468 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,16,14,15,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2468 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2468_checked : acceptsGraphIso
    (source (graph core2468) (root 10) 0 4) DegreeTwoThreeSpectrum5417.graph sourceMap2468=true := by decide +kernel
theorem fusedMap2468_checked : acceptsGraphIso
    (fused (graph core2468) (root 10) 0 4) DegreeTwoThreeSpectrum5001.graph fusedMap2468=true := by decide +kernel
theorem certified2468 : Certified (graph core2468) (root 10) 0 4 :=
  of_native_maps core2468 DegreeTwoThreeSpectrum5417.graph DegreeTwoThreeSpectrum5001.graph
    sourceMap2468 fusedMap2468 sourceMap2468_checked fusedMap2468_checked
    DegreeTwoThreeFiniteComparisons.comparison2468
#print axioms sourceMap2468_checked
#print axioms fusedMap2468_checked
#print axioms certified2468
def sourceMap2468swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,16,14,9,10,11,12,13,15] (sourceLabel 10 4 0 v)
def fusedMap2468swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2468swap_checked : acceptsGraphIso
    (source (graph core2468) (root 10) 4 0) DegreeTwoThreeSpectrum5417.graph sourceMap2468swap=true := by decide +kernel
theorem fusedMap2468swap_checked : acceptsGraphIso
    (fused (graph core2468) (root 10) 4 0) DegreeTwoThreeSpectrum5001.graph fusedMap2468swap=true := by decide +kernel
theorem certified2468swap : Certified (graph core2468) (root 10) 4 0 :=
  of_native_maps core2468 DegreeTwoThreeSpectrum5417.graph DegreeTwoThreeSpectrum5001.graph
    sourceMap2468swap fusedMap2468swap sourceMap2468swap_checked fusedMap2468swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2468
#print axioms sourceMap2468swap_checked
#print axioms fusedMap2468swap_checked
#print axioms certified2468swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
