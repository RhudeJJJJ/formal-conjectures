/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2453 : Family 9 := level9.get ⟨696,by decide⟩
def sourceMap2453 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2453 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2453_checked : acceptsGraphIso
    (source (graph core2453) (root 9) 0 4) DegreeTwoThreeSpectrum4677.graph sourceMap2453=true := by decide +kernel
theorem fusedMap2453_checked : acceptsGraphIso
    (fused (graph core2453) (root 9) 0 4) DegreeTwoThreeSpectrum4678.graph fusedMap2453=true := by decide +kernel
theorem certified2453 : Certified (graph core2453) (root 9) 0 4 :=
  of_native_maps core2453 DegreeTwoThreeSpectrum4677.graph DegreeTwoThreeSpectrum4678.graph
    sourceMap2453 fusedMap2453 sourceMap2453_checked fusedMap2453_checked
    DegreeTwoThreeFiniteComparisons.comparison2453
#print axioms sourceMap2453_checked
#print axioms fusedMap2453_checked
#print axioms certified2453
def sourceMap2453swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2453swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2453swap_checked : acceptsGraphIso
    (source (graph core2453) (root 9) 4 0) DegreeTwoThreeSpectrum4677.graph sourceMap2453swap=true := by decide +kernel
theorem fusedMap2453swap_checked : acceptsGraphIso
    (fused (graph core2453) (root 9) 4 0) DegreeTwoThreeSpectrum4678.graph fusedMap2453swap=true := by decide +kernel
theorem certified2453swap : Certified (graph core2453) (root 9) 4 0 :=
  of_native_maps core2453 DegreeTwoThreeSpectrum4677.graph DegreeTwoThreeSpectrum4678.graph
    sourceMap2453swap fusedMap2453swap sourceMap2453swap_checked fusedMap2453swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2453
#print axioms sourceMap2453swap_checked
#print axioms fusedMap2453swap_checked
#print axioms certified2453swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
