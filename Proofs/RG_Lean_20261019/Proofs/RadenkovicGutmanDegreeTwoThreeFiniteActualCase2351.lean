/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2351 : Family 9 := level9.get ⟨429,by decide⟩
def sourceMap2351 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2351 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2351_checked : acceptsGraphIso
    (source (graph core2351) (root 9) 0 4) DegreeTwoThreeSpectrum4422.graph sourceMap2351=true := by decide +kernel
theorem fusedMap2351_checked : acceptsGraphIso
    (fused (graph core2351) (root 9) 0 4) DegreeTwoThreeSpectrum4423.graph fusedMap2351=true := by decide +kernel
theorem certified2351 : Certified (graph core2351) (root 9) 0 4 :=
  of_native_maps core2351 DegreeTwoThreeSpectrum4422.graph DegreeTwoThreeSpectrum4423.graph
    sourceMap2351 fusedMap2351 sourceMap2351_checked fusedMap2351_checked
    DegreeTwoThreeFiniteComparisons.comparison2351
#print axioms sourceMap2351_checked
#print axioms fusedMap2351_checked
#print axioms certified2351
def sourceMap2351swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2351swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2351swap_checked : acceptsGraphIso
    (source (graph core2351) (root 9) 4 0) DegreeTwoThreeSpectrum4422.graph sourceMap2351swap=true := by decide +kernel
theorem fusedMap2351swap_checked : acceptsGraphIso
    (fused (graph core2351) (root 9) 4 0) DegreeTwoThreeSpectrum4423.graph fusedMap2351swap=true := by decide +kernel
theorem certified2351swap : Certified (graph core2351) (root 9) 4 0 :=
  of_native_maps core2351 DegreeTwoThreeSpectrum4422.graph DegreeTwoThreeSpectrum4423.graph
    sourceMap2351swap fusedMap2351swap sourceMap2351swap_checked fusedMap2351swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2351
#print axioms sourceMap2351swap_checked
#print axioms fusedMap2351swap_checked
#print axioms certified2351swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
