/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2373 : Family 9 := level9.get ⟨478,by decide⟩
def sourceMap2373 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2373 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2373_checked : acceptsGraphIso
    (source (graph core2373) (root 9) 0 4) DegreeTwoThreeSpectrum4518.graph sourceMap2373=true := by decide +kernel
theorem fusedMap2373_checked : acceptsGraphIso
    (fused (graph core2373) (root 9) 0 4) DegreeTwoThreeSpectrum4519.graph fusedMap2373=true := by decide +kernel
theorem certified2373 : Certified (graph core2373) (root 9) 0 4 :=
  of_native_maps core2373 DegreeTwoThreeSpectrum4518.graph DegreeTwoThreeSpectrum4519.graph
    sourceMap2373 fusedMap2373 sourceMap2373_checked fusedMap2373_checked
    DegreeTwoThreeFiniteComparisons.comparison2373
#print axioms sourceMap2373_checked
#print axioms fusedMap2373_checked
#print axioms certified2373
def sourceMap2373swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2373swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2373swap_checked : acceptsGraphIso
    (source (graph core2373) (root 9) 4 0) DegreeTwoThreeSpectrum4518.graph sourceMap2373swap=true := by decide +kernel
theorem fusedMap2373swap_checked : acceptsGraphIso
    (fused (graph core2373) (root 9) 4 0) DegreeTwoThreeSpectrum4519.graph fusedMap2373swap=true := by decide +kernel
theorem certified2373swap : Certified (graph core2373) (root 9) 4 0 :=
  of_native_maps core2373 DegreeTwoThreeSpectrum4518.graph DegreeTwoThreeSpectrum4519.graph
    sourceMap2373swap fusedMap2373swap sourceMap2373swap_checked fusedMap2373swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2373
#print axioms sourceMap2373swap_checked
#print axioms fusedMap2373swap_checked
#print axioms certified2373swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
