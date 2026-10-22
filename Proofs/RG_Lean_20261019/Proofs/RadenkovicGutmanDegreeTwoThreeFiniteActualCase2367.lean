/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2367 : Family 9 := level9.get ⟨467,by decide⟩
def sourceMap2367 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2367 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2367_checked : acceptsGraphIso
    (source (graph core2367) (root 9) 0 4) DegreeTwoThreeSpectrum4497.graph sourceMap2367=true := by decide +kernel
theorem fusedMap2367_checked : acceptsGraphIso
    (fused (graph core2367) (root 9) 0 4) DegreeTwoThreeSpectrum4498.graph fusedMap2367=true := by decide +kernel
theorem certified2367 : Certified (graph core2367) (root 9) 0 4 :=
  of_native_maps core2367 DegreeTwoThreeSpectrum4497.graph DegreeTwoThreeSpectrum4498.graph
    sourceMap2367 fusedMap2367 sourceMap2367_checked fusedMap2367_checked
    DegreeTwoThreeFiniteComparisons.comparison2367
#print axioms sourceMap2367_checked
#print axioms fusedMap2367_checked
#print axioms certified2367
def sourceMap2367swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2367swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2367swap_checked : acceptsGraphIso
    (source (graph core2367) (root 9) 4 0) DegreeTwoThreeSpectrum4497.graph sourceMap2367swap=true := by decide +kernel
theorem fusedMap2367swap_checked : acceptsGraphIso
    (fused (graph core2367) (root 9) 4 0) DegreeTwoThreeSpectrum4498.graph fusedMap2367swap=true := by decide +kernel
theorem certified2367swap : Certified (graph core2367) (root 9) 4 0 :=
  of_native_maps core2367 DegreeTwoThreeSpectrum4497.graph DegreeTwoThreeSpectrum4498.graph
    sourceMap2367swap fusedMap2367swap sourceMap2367swap_checked fusedMap2367swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2367
#print axioms sourceMap2367swap_checked
#print axioms fusedMap2367swap_checked
#print axioms certified2367swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
