/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3426 : Family 9 := level9.get ⟨557,by decide⟩
def sourceMap3426 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3426 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3426_checked : acceptsGraphIso
    (source (graph core3426) (root 9) 0 5) DegreeTwoThreeSpectrum6023.graph sourceMap3426=true := by decide +kernel
theorem fusedMap3426_checked : acceptsGraphIso
    (fused (graph core3426) (root 9) 0 5) DegreeTwoThreeSpectrum6024.graph fusedMap3426=true := by decide +kernel
theorem certified3426 : Certified (graph core3426) (root 9) 0 5 :=
  of_native_maps core3426 DegreeTwoThreeSpectrum6023.graph DegreeTwoThreeSpectrum6024.graph
    sourceMap3426 fusedMap3426 sourceMap3426_checked fusedMap3426_checked
    DegreeTwoThreeFiniteComparisons.comparison3426
#print axioms sourceMap3426_checked
#print axioms fusedMap3426_checked
#print axioms certified3426
def sourceMap3426swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3426swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3426swap_checked : acceptsGraphIso
    (source (graph core3426) (root 9) 5 0) DegreeTwoThreeSpectrum6023.graph sourceMap3426swap=true := by decide +kernel
theorem fusedMap3426swap_checked : acceptsGraphIso
    (fused (graph core3426) (root 9) 5 0) DegreeTwoThreeSpectrum6024.graph fusedMap3426swap=true := by decide +kernel
theorem certified3426swap : Certified (graph core3426) (root 9) 5 0 :=
  of_native_maps core3426 DegreeTwoThreeSpectrum6023.graph DegreeTwoThreeSpectrum6024.graph
    sourceMap3426swap fusedMap3426swap sourceMap3426swap_checked fusedMap3426swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3426
#print axioms sourceMap3426swap_checked
#print axioms fusedMap3426swap_checked
#print axioms certified3426swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
