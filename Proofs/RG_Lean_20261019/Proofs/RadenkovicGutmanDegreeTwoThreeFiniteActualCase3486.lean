/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3486 : Family 6 := level6.get ⟨5,by decide⟩
def sourceMap3486 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (sourceLabel 6 0 6 v)
def fusedMap3486 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13,14] (fusedLabel 6 0 6 v)
theorem sourceMap3486_checked : acceptsGraphIso
    (source (graph core3486) (root 6) 0 6) DegreeTwoThreeSpectrum2433.graph sourceMap3486=true := by decide +kernel
theorem fusedMap3486_checked : acceptsGraphIso
    (fused (graph core3486) (root 6) 0 6) DegreeTwoThreeSpectrum2313.graph fusedMap3486=true := by decide +kernel
theorem certified3486 : Certified (graph core3486) (root 6) 0 6 :=
  of_native_maps core3486 DegreeTwoThreeSpectrum2433.graph DegreeTwoThreeSpectrum2313.graph
    sourceMap3486 fusedMap3486 sourceMap3486_checked fusedMap3486_checked
    DegreeTwoThreeFiniteComparisons.comparison3486
#print axioms sourceMap3486_checked
#print axioms fusedMap3486_checked
#print axioms certified3486
def sourceMap3486swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,13,14,8] (sourceLabel 6 6 0 v)
def fusedMap3486swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13,14] (fusedLabel 6 6 0 v)
theorem sourceMap3486swap_checked : acceptsGraphIso
    (source (graph core3486) (root 6) 6 0) DegreeTwoThreeSpectrum2433.graph sourceMap3486swap=true := by decide +kernel
theorem fusedMap3486swap_checked : acceptsGraphIso
    (fused (graph core3486) (root 6) 6 0) DegreeTwoThreeSpectrum2313.graph fusedMap3486swap=true := by decide +kernel
theorem certified3486swap : Certified (graph core3486) (root 6) 6 0 :=
  of_native_maps core3486 DegreeTwoThreeSpectrum2433.graph DegreeTwoThreeSpectrum2313.graph
    sourceMap3486swap fusedMap3486swap sourceMap3486swap_checked fusedMap3486swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3486
#print axioms sourceMap3486swap_checked
#print axioms fusedMap3486swap_checked
#print axioms certified3486swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
