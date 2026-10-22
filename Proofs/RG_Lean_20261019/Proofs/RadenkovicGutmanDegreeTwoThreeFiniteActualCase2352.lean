/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2352 : Family 9 := level9.get ⟨431,by decide⟩
def sourceMap2352 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2352 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2352_checked : acceptsGraphIso
    (source (graph core2352) (root 9) 0 4) DegreeTwoThreeSpectrum4424.graph sourceMap2352=true := by decide +kernel
theorem fusedMap2352_checked : acceptsGraphIso
    (fused (graph core2352) (root 9) 0 4) DegreeTwoThreeSpectrum4425.graph fusedMap2352=true := by decide +kernel
theorem certified2352 : Certified (graph core2352) (root 9) 0 4 :=
  of_native_maps core2352 DegreeTwoThreeSpectrum4424.graph DegreeTwoThreeSpectrum4425.graph
    sourceMap2352 fusedMap2352 sourceMap2352_checked fusedMap2352_checked
    DegreeTwoThreeFiniteComparisons.comparison2352
#print axioms sourceMap2352_checked
#print axioms fusedMap2352_checked
#print axioms certified2352
def sourceMap2352swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2352swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2352swap_checked : acceptsGraphIso
    (source (graph core2352) (root 9) 4 0) DegreeTwoThreeSpectrum4424.graph sourceMap2352swap=true := by decide +kernel
theorem fusedMap2352swap_checked : acceptsGraphIso
    (fused (graph core2352) (root 9) 4 0) DegreeTwoThreeSpectrum4425.graph fusedMap2352swap=true := by decide +kernel
theorem certified2352swap : Certified (graph core2352) (root 9) 4 0 :=
  of_native_maps core2352 DegreeTwoThreeSpectrum4424.graph DegreeTwoThreeSpectrum4425.graph
    sourceMap2352swap fusedMap2352swap sourceMap2352swap_checked fusedMap2352swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2352
#print axioms sourceMap2352swap_checked
#print axioms fusedMap2352swap_checked
#print axioms certified2352swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
