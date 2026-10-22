/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3464 : Family 9 := level9.get ⟨651,by decide⟩
def sourceMap3464 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3464 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3464_checked : acceptsGraphIso
    (source (graph core3464) (root 9) 0 5) DegreeTwoThreeSpectrum6588.graph sourceMap3464=true := by decide +kernel
theorem fusedMap3464_checked : acceptsGraphIso
    (fused (graph core3464) (root 9) 0 5) DegreeTwoThreeSpectrum6589.graph fusedMap3464=true := by decide +kernel
theorem certified3464 : Certified (graph core3464) (root 9) 0 5 :=
  of_native_maps core3464 DegreeTwoThreeSpectrum6588.graph DegreeTwoThreeSpectrum6589.graph
    sourceMap3464 fusedMap3464 sourceMap3464_checked fusedMap3464_checked
    DegreeTwoThreeFiniteComparisons.comparison3464
#print axioms sourceMap3464_checked
#print axioms fusedMap3464_checked
#print axioms certified3464
def sourceMap3464swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3464swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3464swap_checked : acceptsGraphIso
    (source (graph core3464) (root 9) 5 0) DegreeTwoThreeSpectrum6588.graph sourceMap3464swap=true := by decide +kernel
theorem fusedMap3464swap_checked : acceptsGraphIso
    (fused (graph core3464) (root 9) 5 0) DegreeTwoThreeSpectrum6589.graph fusedMap3464swap=true := by decide +kernel
theorem certified3464swap : Certified (graph core3464) (root 9) 5 0 :=
  of_native_maps core3464 DegreeTwoThreeSpectrum6588.graph DegreeTwoThreeSpectrum6589.graph
    sourceMap3464swap fusedMap3464swap sourceMap3464swap_checked fusedMap3464swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3464
#print axioms sourceMap3464swap_checked
#print axioms fusedMap3464swap_checked
#print axioms certified3464swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
