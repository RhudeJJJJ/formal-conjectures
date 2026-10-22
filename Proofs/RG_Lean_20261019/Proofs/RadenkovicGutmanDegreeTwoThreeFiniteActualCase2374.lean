/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2374 : Family 9 := level9.get ⟨479,by decide⟩
def sourceMap2374 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2374 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2374_checked : acceptsGraphIso
    (source (graph core2374) (root 9) 0 4) DegreeTwoThreeSpectrum4520.graph sourceMap2374=true := by decide +kernel
theorem fusedMap2374_checked : acceptsGraphIso
    (fused (graph core2374) (root 9) 0 4) DegreeTwoThreeSpectrum4521.graph fusedMap2374=true := by decide +kernel
theorem certified2374 : Certified (graph core2374) (root 9) 0 4 :=
  of_native_maps core2374 DegreeTwoThreeSpectrum4520.graph DegreeTwoThreeSpectrum4521.graph
    sourceMap2374 fusedMap2374 sourceMap2374_checked fusedMap2374_checked
    DegreeTwoThreeFiniteComparisons.comparison2374
#print axioms sourceMap2374_checked
#print axioms fusedMap2374_checked
#print axioms certified2374
def sourceMap2374swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2374swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2374swap_checked : acceptsGraphIso
    (source (graph core2374) (root 9) 4 0) DegreeTwoThreeSpectrum4520.graph sourceMap2374swap=true := by decide +kernel
theorem fusedMap2374swap_checked : acceptsGraphIso
    (fused (graph core2374) (root 9) 4 0) DegreeTwoThreeSpectrum4521.graph fusedMap2374swap=true := by decide +kernel
theorem certified2374swap : Certified (graph core2374) (root 9) 4 0 :=
  of_native_maps core2374 DegreeTwoThreeSpectrum4520.graph DegreeTwoThreeSpectrum4521.graph
    sourceMap2374swap fusedMap2374swap sourceMap2374swap_checked fusedMap2374swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2374
#print axioms sourceMap2374swap_checked
#print axioms fusedMap2374swap_checked
#print axioms certified2374swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
