/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2358 : Family 9 := level9.get ⟨444,by decide⟩
def sourceMap2358 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2358 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2358_checked : acceptsGraphIso
    (source (graph core2358) (root 9) 0 4) DegreeTwoThreeSpectrum4452.graph sourceMap2358=true := by decide +kernel
theorem fusedMap2358_checked : acceptsGraphIso
    (fused (graph core2358) (root 9) 0 4) DegreeTwoThreeSpectrum4453.graph fusedMap2358=true := by decide +kernel
theorem certified2358 : Certified (graph core2358) (root 9) 0 4 :=
  of_native_maps core2358 DegreeTwoThreeSpectrum4452.graph DegreeTwoThreeSpectrum4453.graph
    sourceMap2358 fusedMap2358 sourceMap2358_checked fusedMap2358_checked
    DegreeTwoThreeFiniteComparisons.comparison2358
#print axioms sourceMap2358_checked
#print axioms fusedMap2358_checked
#print axioms certified2358
def sourceMap2358swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2358swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2358swap_checked : acceptsGraphIso
    (source (graph core2358) (root 9) 4 0) DegreeTwoThreeSpectrum4452.graph sourceMap2358swap=true := by decide +kernel
theorem fusedMap2358swap_checked : acceptsGraphIso
    (fused (graph core2358) (root 9) 4 0) DegreeTwoThreeSpectrum4453.graph fusedMap2358swap=true := by decide +kernel
theorem certified2358swap : Certified (graph core2358) (root 9) 4 0 :=
  of_native_maps core2358 DegreeTwoThreeSpectrum4452.graph DegreeTwoThreeSpectrum4453.graph
    sourceMap2358swap fusedMap2358swap sourceMap2358swap_checked fusedMap2358swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2358
#print axioms sourceMap2358swap_checked
#print axioms fusedMap2358swap_checked
#print axioms certified2358swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
