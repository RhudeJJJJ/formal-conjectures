/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2295 : Family 9 := level9.get ⟨281,by decide⟩
def sourceMap2295 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12] (sourceLabel 9 0 4 v)
def fusedMap2295 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2295_checked : acceptsGraphIso
    (source (graph core2295) (root 9) 0 4) DegreeTwoThreeSpectrum4622.graph sourceMap2295=true := by decide +kernel
theorem fusedMap2295_checked : acceptsGraphIso
    (fused (graph core2295) (root 9) 0 4) DegreeTwoThreeSpectrum4099.graph fusedMap2295=true := by decide +kernel
theorem certified2295 : Certified (graph core2295) (root 9) 0 4 :=
  of_native_maps core2295 DegreeTwoThreeSpectrum4622.graph DegreeTwoThreeSpectrum4099.graph
    sourceMap2295 fusedMap2295 sourceMap2295_checked fusedMap2295_checked
    DegreeTwoThreeFiniteComparisons.comparison2295
#print axioms sourceMap2295_checked
#print axioms fusedMap2295_checked
#print axioms certified2295
def sourceMap2295swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12,15] (sourceLabel 9 4 0 v)
def fusedMap2295swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2295swap_checked : acceptsGraphIso
    (source (graph core2295) (root 9) 4 0) DegreeTwoThreeSpectrum4622.graph sourceMap2295swap=true := by decide +kernel
theorem fusedMap2295swap_checked : acceptsGraphIso
    (fused (graph core2295) (root 9) 4 0) DegreeTwoThreeSpectrum4099.graph fusedMap2295swap=true := by decide +kernel
theorem certified2295swap : Certified (graph core2295) (root 9) 4 0 :=
  of_native_maps core2295 DegreeTwoThreeSpectrum4622.graph DegreeTwoThreeSpectrum4099.graph
    sourceMap2295swap fusedMap2295swap sourceMap2295swap_checked fusedMap2295swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2295
#print axioms sourceMap2295swap_checked
#print axioms fusedMap2295swap_checked
#print axioms certified2295swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
