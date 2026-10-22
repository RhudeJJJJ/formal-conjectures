/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2381 : Family 9 := level9.get ⟨500,by decide⟩
def sourceMap2381 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2381 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2381_checked : acceptsGraphIso
    (source (graph core2381) (root 9) 0 4) DegreeTwoThreeSpectrum4577.graph sourceMap2381=true := by decide +kernel
theorem fusedMap2381_checked : acceptsGraphIso
    (fused (graph core2381) (root 9) 0 4) DegreeTwoThreeSpectrum4578.graph fusedMap2381=true := by decide +kernel
theorem certified2381 : Certified (graph core2381) (root 9) 0 4 :=
  of_native_maps core2381 DegreeTwoThreeSpectrum4577.graph DegreeTwoThreeSpectrum4578.graph
    sourceMap2381 fusedMap2381 sourceMap2381_checked fusedMap2381_checked
    DegreeTwoThreeFiniteComparisons.comparison2381
#print axioms sourceMap2381_checked
#print axioms fusedMap2381_checked
#print axioms certified2381
def sourceMap2381swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2381swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2381swap_checked : acceptsGraphIso
    (source (graph core2381) (root 9) 4 0) DegreeTwoThreeSpectrum4577.graph sourceMap2381swap=true := by decide +kernel
theorem fusedMap2381swap_checked : acceptsGraphIso
    (fused (graph core2381) (root 9) 4 0) DegreeTwoThreeSpectrum4578.graph fusedMap2381swap=true := by decide +kernel
theorem certified2381swap : Certified (graph core2381) (root 9) 4 0 :=
  of_native_maps core2381 DegreeTwoThreeSpectrum4577.graph DegreeTwoThreeSpectrum4578.graph
    sourceMap2381swap fusedMap2381swap sourceMap2381swap_checked fusedMap2381swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2381
#print axioms sourceMap2381swap_checked
#print axioms fusedMap2381swap_checked
#print axioms certified2381swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
