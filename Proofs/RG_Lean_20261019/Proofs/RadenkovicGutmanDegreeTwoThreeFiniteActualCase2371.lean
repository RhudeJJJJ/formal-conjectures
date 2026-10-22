/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2371 : Family 9 := level9.get ⟨474,by decide⟩
def sourceMap2371 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2371 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2371_checked : acceptsGraphIso
    (source (graph core2371) (root 9) 0 4) DegreeTwoThreeSpectrum4509.graph sourceMap2371=true := by decide +kernel
theorem fusedMap2371_checked : acceptsGraphIso
    (fused (graph core2371) (root 9) 0 4) DegreeTwoThreeSpectrum4510.graph fusedMap2371=true := by decide +kernel
theorem certified2371 : Certified (graph core2371) (root 9) 0 4 :=
  of_native_maps core2371 DegreeTwoThreeSpectrum4509.graph DegreeTwoThreeSpectrum4510.graph
    sourceMap2371 fusedMap2371 sourceMap2371_checked fusedMap2371_checked
    DegreeTwoThreeFiniteComparisons.comparison2371
#print axioms sourceMap2371_checked
#print axioms fusedMap2371_checked
#print axioms certified2371
def sourceMap2371swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2371swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2371swap_checked : acceptsGraphIso
    (source (graph core2371) (root 9) 4 0) DegreeTwoThreeSpectrum4509.graph sourceMap2371swap=true := by decide +kernel
theorem fusedMap2371swap_checked : acceptsGraphIso
    (fused (graph core2371) (root 9) 4 0) DegreeTwoThreeSpectrum4510.graph fusedMap2371swap=true := by decide +kernel
theorem certified2371swap : Certified (graph core2371) (root 9) 4 0 :=
  of_native_maps core2371 DegreeTwoThreeSpectrum4509.graph DegreeTwoThreeSpectrum4510.graph
    sourceMap2371swap fusedMap2371swap sourceMap2371swap_checked fusedMap2371swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2371
#print axioms sourceMap2371swap_checked
#print axioms fusedMap2371swap_checked
#print axioms certified2371swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
