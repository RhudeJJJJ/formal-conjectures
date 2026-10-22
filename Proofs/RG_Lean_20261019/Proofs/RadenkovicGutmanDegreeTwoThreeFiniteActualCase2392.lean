/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2392 : Family 9 := level9.get ⟨519,by decide⟩
def sourceMap2392 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2392 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2392_checked : acceptsGraphIso
    (source (graph core2392) (root 9) 0 4) DegreeTwoThreeSpectrum4611.graph sourceMap2392=true := by decide +kernel
theorem fusedMap2392_checked : acceptsGraphIso
    (fused (graph core2392) (root 9) 0 4) DegreeTwoThreeSpectrum4612.graph fusedMap2392=true := by decide +kernel
theorem certified2392 : Certified (graph core2392) (root 9) 0 4 :=
  of_native_maps core2392 DegreeTwoThreeSpectrum4611.graph DegreeTwoThreeSpectrum4612.graph
    sourceMap2392 fusedMap2392 sourceMap2392_checked fusedMap2392_checked
    DegreeTwoThreeFiniteComparisons.comparison2392
#print axioms sourceMap2392_checked
#print axioms fusedMap2392_checked
#print axioms certified2392
def sourceMap2392swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2392swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2392swap_checked : acceptsGraphIso
    (source (graph core2392) (root 9) 4 0) DegreeTwoThreeSpectrum4611.graph sourceMap2392swap=true := by decide +kernel
theorem fusedMap2392swap_checked : acceptsGraphIso
    (fused (graph core2392) (root 9) 4 0) DegreeTwoThreeSpectrum4612.graph fusedMap2392swap=true := by decide +kernel
theorem certified2392swap : Certified (graph core2392) (root 9) 4 0 :=
  of_native_maps core2392 DegreeTwoThreeSpectrum4611.graph DegreeTwoThreeSpectrum4612.graph
    sourceMap2392swap fusedMap2392swap sourceMap2392swap_checked fusedMap2392swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2392
#print axioms sourceMap2392swap_checked
#print axioms fusedMap2392swap_checked
#print axioms certified2392swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
