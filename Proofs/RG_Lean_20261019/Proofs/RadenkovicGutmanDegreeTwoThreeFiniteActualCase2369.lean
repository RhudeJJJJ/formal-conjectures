/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2369 : Family 9 := level9.get ⟨471,by decide⟩
def sourceMap2369 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2369 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2369_checked : acceptsGraphIso
    (source (graph core2369) (root 9) 0 4) DegreeTwoThreeSpectrum4503.graph sourceMap2369=true := by decide +kernel
theorem fusedMap2369_checked : acceptsGraphIso
    (fused (graph core2369) (root 9) 0 4) DegreeTwoThreeSpectrum4504.graph fusedMap2369=true := by decide +kernel
theorem certified2369 : Certified (graph core2369) (root 9) 0 4 :=
  of_native_maps core2369 DegreeTwoThreeSpectrum4503.graph DegreeTwoThreeSpectrum4504.graph
    sourceMap2369 fusedMap2369 sourceMap2369_checked fusedMap2369_checked
    DegreeTwoThreeFiniteComparisons.comparison2369
#print axioms sourceMap2369_checked
#print axioms fusedMap2369_checked
#print axioms certified2369
def sourceMap2369swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2369swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2369swap_checked : acceptsGraphIso
    (source (graph core2369) (root 9) 4 0) DegreeTwoThreeSpectrum4503.graph sourceMap2369swap=true := by decide +kernel
theorem fusedMap2369swap_checked : acceptsGraphIso
    (fused (graph core2369) (root 9) 4 0) DegreeTwoThreeSpectrum4504.graph fusedMap2369swap=true := by decide +kernel
theorem certified2369swap : Certified (graph core2369) (root 9) 4 0 :=
  of_native_maps core2369 DegreeTwoThreeSpectrum4503.graph DegreeTwoThreeSpectrum4504.graph
    sourceMap2369swap fusedMap2369swap sourceMap2369swap_checked fusedMap2369swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2369
#print axioms sourceMap2369swap_checked
#print axioms fusedMap2369swap_checked
#print axioms certified2369swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
