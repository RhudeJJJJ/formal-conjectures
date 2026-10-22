/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2284 : Family 9 := level9.get ⟨248,by decide⟩
def sourceMap2284 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11] (sourceLabel 9 0 4 v)
def fusedMap2284 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2284_checked : acceptsGraphIso
    (source (graph core2284) (root 9) 0 4) DegreeTwoThreeSpectrum4537.graph sourceMap2284=true := by decide +kernel
theorem fusedMap2284_checked : acceptsGraphIso
    (fused (graph core2284) (root 9) 0 4) DegreeTwoThreeSpectrum4049.graph fusedMap2284=true := by decide +kernel
theorem certified2284 : Certified (graph core2284) (root 9) 0 4 :=
  of_native_maps core2284 DegreeTwoThreeSpectrum4537.graph DegreeTwoThreeSpectrum4049.graph
    sourceMap2284 fusedMap2284 sourceMap2284_checked fusedMap2284_checked
    DegreeTwoThreeFiniteComparisons.comparison2284
#print axioms sourceMap2284_checked
#print axioms fusedMap2284_checked
#print axioms certified2284
def sourceMap2284swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,7,8,9,10,11,15] (sourceLabel 9 4 0 v)
def fusedMap2284swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2284swap_checked : acceptsGraphIso
    (source (graph core2284) (root 9) 4 0) DegreeTwoThreeSpectrum4537.graph sourceMap2284swap=true := by decide +kernel
theorem fusedMap2284swap_checked : acceptsGraphIso
    (fused (graph core2284) (root 9) 4 0) DegreeTwoThreeSpectrum4049.graph fusedMap2284swap=true := by decide +kernel
theorem certified2284swap : Certified (graph core2284) (root 9) 4 0 :=
  of_native_maps core2284 DegreeTwoThreeSpectrum4537.graph DegreeTwoThreeSpectrum4049.graph
    sourceMap2284swap fusedMap2284swap sourceMap2284swap_checked fusedMap2284swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2284
#print axioms sourceMap2284swap_checked
#print axioms fusedMap2284swap_checked
#print axioms certified2284swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
