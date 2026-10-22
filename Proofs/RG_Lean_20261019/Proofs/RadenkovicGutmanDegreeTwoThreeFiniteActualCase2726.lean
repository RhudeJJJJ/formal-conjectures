/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2726 : Family 10 := level10.get ⟨889,by decide⟩
def sourceMap2726 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2726 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2726_checked : acceptsGraphIso
    (source (graph core2726) (root 10) 0 4) DegreeTwoThreeSpectrum6957.graph sourceMap2726=true := by decide +kernel
theorem fusedMap2726_checked : acceptsGraphIso
    (fused (graph core2726) (root 10) 0 4) DegreeTwoThreeSpectrum5744.graph fusedMap2726=true := by decide +kernel
theorem certified2726 : Certified (graph core2726) (root 10) 0 4 :=
  of_native_maps core2726 DegreeTwoThreeSpectrum6957.graph DegreeTwoThreeSpectrum5744.graph
    sourceMap2726 fusedMap2726 sourceMap2726_checked fusedMap2726_checked
    DegreeTwoThreeFiniteComparisons.comparison2726
#print axioms sourceMap2726_checked
#print axioms fusedMap2726_checked
#print axioms certified2726
def sourceMap2726swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2726swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2726swap_checked : acceptsGraphIso
    (source (graph core2726) (root 10) 4 0) DegreeTwoThreeSpectrum6957.graph sourceMap2726swap=true := by decide +kernel
theorem fusedMap2726swap_checked : acceptsGraphIso
    (fused (graph core2726) (root 10) 4 0) DegreeTwoThreeSpectrum5744.graph fusedMap2726swap=true := by decide +kernel
theorem certified2726swap : Certified (graph core2726) (root 10) 4 0 :=
  of_native_maps core2726 DegreeTwoThreeSpectrum6957.graph DegreeTwoThreeSpectrum5744.graph
    sourceMap2726swap fusedMap2726swap sourceMap2726swap_checked fusedMap2726swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2726
#print axioms sourceMap2726swap_checked
#print axioms fusedMap2726swap_checked
#print axioms certified2726swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
