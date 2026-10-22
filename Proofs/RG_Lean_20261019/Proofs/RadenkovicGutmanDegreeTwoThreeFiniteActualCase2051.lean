/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2051 : Family 10 := level10.get ⟨1807,by decide⟩
def sourceMap2051 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 0 2 v)
def fusedMap2051 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2051_checked : acceptsGraphIso
    (source (graph core2051) (root 10) 0 2) DegreeTwoThreeSpectrum3740.graph sourceMap2051=true := by decide +kernel
theorem fusedMap2051_checked : acceptsGraphIso
    (fused (graph core2051) (root 10) 0 2) DegreeTwoThreeSpectrum3741.graph fusedMap2051=true := by decide +kernel
theorem certified2051 : Certified (graph core2051) (root 10) 0 2 :=
  of_native_maps core2051 DegreeTwoThreeSpectrum3740.graph DegreeTwoThreeSpectrum3741.graph
    sourceMap2051 fusedMap2051 sourceMap2051_checked fusedMap2051_checked
    DegreeTwoThreeFiniteComparisons.comparison2051
#print axioms sourceMap2051_checked
#print axioms fusedMap2051_checked
#print axioms certified2051
def sourceMap2051swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,11] (sourceLabel 10 2 0 v)
def fusedMap2051swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2051swap_checked : acceptsGraphIso
    (source (graph core2051) (root 10) 2 0) DegreeTwoThreeSpectrum3740.graph sourceMap2051swap=true := by decide +kernel
theorem fusedMap2051swap_checked : acceptsGraphIso
    (fused (graph core2051) (root 10) 2 0) DegreeTwoThreeSpectrum3741.graph fusedMap2051swap=true := by decide +kernel
theorem certified2051swap : Certified (graph core2051) (root 10) 2 0 :=
  of_native_maps core2051 DegreeTwoThreeSpectrum3740.graph DegreeTwoThreeSpectrum3741.graph
    sourceMap2051swap fusedMap2051swap sourceMap2051swap_checked fusedMap2051swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2051
#print axioms sourceMap2051swap_checked
#print axioms fusedMap2051swap_checked
#print axioms certified2051swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
