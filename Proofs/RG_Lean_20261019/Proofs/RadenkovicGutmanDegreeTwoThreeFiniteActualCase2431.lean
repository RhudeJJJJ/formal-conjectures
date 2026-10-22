/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2431 : Family 9 := level9.get ⟨617,by decide⟩
def sourceMap2431 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2431 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2431_checked : acceptsGraphIso
    (source (graph core2431) (root 9) 0 4) DegreeTwoThreeSpectrum4759.graph sourceMap2431=true := by decide +kernel
theorem fusedMap2431_checked : acceptsGraphIso
    (fused (graph core2431) (root 9) 0 4) DegreeTwoThreeSpectrum4331.graph fusedMap2431=true := by decide +kernel
theorem certified2431 : Certified (graph core2431) (root 9) 0 4 :=
  of_native_maps core2431 DegreeTwoThreeSpectrum4759.graph DegreeTwoThreeSpectrum4331.graph
    sourceMap2431 fusedMap2431 sourceMap2431_checked fusedMap2431_checked
    DegreeTwoThreeFiniteComparisons.comparison2431
#print axioms sourceMap2431_checked
#print axioms fusedMap2431_checked
#print axioms certified2431
def sourceMap2431swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2431swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2431swap_checked : acceptsGraphIso
    (source (graph core2431) (root 9) 4 0) DegreeTwoThreeSpectrum4759.graph sourceMap2431swap=true := by decide +kernel
theorem fusedMap2431swap_checked : acceptsGraphIso
    (fused (graph core2431) (root 9) 4 0) DegreeTwoThreeSpectrum4331.graph fusedMap2431swap=true := by decide +kernel
theorem certified2431swap : Certified (graph core2431) (root 9) 4 0 :=
  of_native_maps core2431 DegreeTwoThreeSpectrum4759.graph DegreeTwoThreeSpectrum4331.graph
    sourceMap2431swap fusedMap2431swap sourceMap2431swap_checked fusedMap2431swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2431
#print axioms sourceMap2431swap_checked
#print axioms fusedMap2431swap_checked
#print axioms certified2431swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
