/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2368 : Family 9 := level9.get ⟨470,by decide⟩
def sourceMap2368 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2368 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2368_checked : acceptsGraphIso
    (source (graph core2368) (root 9) 0 4) DegreeTwoThreeSpectrum4501.graph sourceMap2368=true := by decide +kernel
theorem fusedMap2368_checked : acceptsGraphIso
    (fused (graph core2368) (root 9) 0 4) DegreeTwoThreeSpectrum4502.graph fusedMap2368=true := by decide +kernel
theorem certified2368 : Certified (graph core2368) (root 9) 0 4 :=
  of_native_maps core2368 DegreeTwoThreeSpectrum4501.graph DegreeTwoThreeSpectrum4502.graph
    sourceMap2368 fusedMap2368 sourceMap2368_checked fusedMap2368_checked
    DegreeTwoThreeFiniteComparisons.comparison2368
#print axioms sourceMap2368_checked
#print axioms fusedMap2368_checked
#print axioms certified2368
def sourceMap2368swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2368swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2368swap_checked : acceptsGraphIso
    (source (graph core2368) (root 9) 4 0) DegreeTwoThreeSpectrum4501.graph sourceMap2368swap=true := by decide +kernel
theorem fusedMap2368swap_checked : acceptsGraphIso
    (fused (graph core2368) (root 9) 4 0) DegreeTwoThreeSpectrum4502.graph fusedMap2368swap=true := by decide +kernel
theorem certified2368swap : Certified (graph core2368) (root 9) 4 0 :=
  of_native_maps core2368 DegreeTwoThreeSpectrum4501.graph DegreeTwoThreeSpectrum4502.graph
    sourceMap2368swap fusedMap2368swap sourceMap2368swap_checked fusedMap2368swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2368
#print axioms sourceMap2368swap_checked
#print axioms fusedMap2368swap_checked
#print axioms certified2368swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
