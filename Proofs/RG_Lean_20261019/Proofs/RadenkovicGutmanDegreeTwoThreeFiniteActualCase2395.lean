/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2395 : Family 9 := level9.get ⟨528,by decide⟩
def sourceMap2395 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2395 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2395_checked : acceptsGraphIso
    (source (graph core2395) (root 9) 0 4) DegreeTwoThreeSpectrum4630.graph sourceMap2395=true := by decide +kernel
theorem fusedMap2395_checked : acceptsGraphIso
    (fused (graph core2395) (root 9) 0 4) DegreeTwoThreeSpectrum4631.graph fusedMap2395=true := by decide +kernel
theorem certified2395 : Certified (graph core2395) (root 9) 0 4 :=
  of_native_maps core2395 DegreeTwoThreeSpectrum4630.graph DegreeTwoThreeSpectrum4631.graph
    sourceMap2395 fusedMap2395 sourceMap2395_checked fusedMap2395_checked
    DegreeTwoThreeFiniteComparisons.comparison2395
#print axioms sourceMap2395_checked
#print axioms fusedMap2395_checked
#print axioms certified2395
def sourceMap2395swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2395swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2395swap_checked : acceptsGraphIso
    (source (graph core2395) (root 9) 4 0) DegreeTwoThreeSpectrum4630.graph sourceMap2395swap=true := by decide +kernel
theorem fusedMap2395swap_checked : acceptsGraphIso
    (fused (graph core2395) (root 9) 4 0) DegreeTwoThreeSpectrum4631.graph fusedMap2395swap=true := by decide +kernel
theorem certified2395swap : Certified (graph core2395) (root 9) 4 0 :=
  of_native_maps core2395 DegreeTwoThreeSpectrum4630.graph DegreeTwoThreeSpectrum4631.graph
    sourceMap2395swap fusedMap2395swap sourceMap2395swap_checked fusedMap2395swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2395
#print axioms sourceMap2395swap_checked
#print axioms fusedMap2395swap_checked
#print axioms certified2395swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
