/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3403 : Family 9 := level9.get ⟨502,by decide⟩
def sourceMap3403 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3403 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3403_checked : acceptsGraphIso
    (source (graph core3403) (root 9) 0 5) DegreeTwoThreeSpectrum6906.graph sourceMap3403=true := by decide +kernel
theorem fusedMap3403_checked : acceptsGraphIso
    (fused (graph core3403) (root 9) 0 5) DegreeTwoThreeSpectrum5692.graph fusedMap3403=true := by decide +kernel
theorem certified3403 : Certified (graph core3403) (root 9) 0 5 :=
  of_native_maps core3403 DegreeTwoThreeSpectrum6906.graph DegreeTwoThreeSpectrum5692.graph
    sourceMap3403 fusedMap3403 sourceMap3403_checked fusedMap3403_checked
    DegreeTwoThreeFiniteComparisons.comparison3403
#print axioms sourceMap3403_checked
#print axioms fusedMap3403_checked
#print axioms certified3403
def sourceMap3403swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3403swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3403swap_checked : acceptsGraphIso
    (source (graph core3403) (root 9) 5 0) DegreeTwoThreeSpectrum6906.graph sourceMap3403swap=true := by decide +kernel
theorem fusedMap3403swap_checked : acceptsGraphIso
    (fused (graph core3403) (root 9) 5 0) DegreeTwoThreeSpectrum5692.graph fusedMap3403swap=true := by decide +kernel
theorem certified3403swap : Certified (graph core3403) (root 9) 5 0 :=
  of_native_maps core3403 DegreeTwoThreeSpectrum6906.graph DegreeTwoThreeSpectrum5692.graph
    sourceMap3403swap fusedMap3403swap sourceMap3403swap_checked fusedMap3403swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3403
#print axioms sourceMap3403swap_checked
#print axioms fusedMap3403swap_checked
#print axioms certified3403swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
