/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2357 : Family 9 := level9.get ⟨443,by decide⟩
def sourceMap2357 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2357 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2357_checked : acceptsGraphIso
    (source (graph core2357) (root 9) 0 4) DegreeTwoThreeSpectrum4450.graph sourceMap2357=true := by decide +kernel
theorem fusedMap2357_checked : acceptsGraphIso
    (fused (graph core2357) (root 9) 0 4) DegreeTwoThreeSpectrum4451.graph fusedMap2357=true := by decide +kernel
theorem certified2357 : Certified (graph core2357) (root 9) 0 4 :=
  of_native_maps core2357 DegreeTwoThreeSpectrum4450.graph DegreeTwoThreeSpectrum4451.graph
    sourceMap2357 fusedMap2357 sourceMap2357_checked fusedMap2357_checked
    DegreeTwoThreeFiniteComparisons.comparison2357
#print axioms sourceMap2357_checked
#print axioms fusedMap2357_checked
#print axioms certified2357
def sourceMap2357swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2357swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2357swap_checked : acceptsGraphIso
    (source (graph core2357) (root 9) 4 0) DegreeTwoThreeSpectrum4450.graph sourceMap2357swap=true := by decide +kernel
theorem fusedMap2357swap_checked : acceptsGraphIso
    (fused (graph core2357) (root 9) 4 0) DegreeTwoThreeSpectrum4451.graph fusedMap2357swap=true := by decide +kernel
theorem certified2357swap : Certified (graph core2357) (root 9) 4 0 :=
  of_native_maps core2357 DegreeTwoThreeSpectrum4450.graph DegreeTwoThreeSpectrum4451.graph
    sourceMap2357swap fusedMap2357swap sourceMap2357swap_checked fusedMap2357swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2357
#print axioms sourceMap2357swap_checked
#print axioms fusedMap2357swap_checked
#print axioms certified2357swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
