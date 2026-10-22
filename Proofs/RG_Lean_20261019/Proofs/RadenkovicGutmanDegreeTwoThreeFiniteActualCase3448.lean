/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3448 : Family 9 := level9.get ⟨605,by decide⟩
def sourceMap3448 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3448 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3448_checked : acceptsGraphIso
    (source (graph core3448) (root 9) 0 5) DegreeTwoThreeSpectrum6259.graph sourceMap3448=true := by decide +kernel
theorem fusedMap3448_checked : acceptsGraphIso
    (fused (graph core3448) (root 9) 0 5) DegreeTwoThreeSpectrum6260.graph fusedMap3448=true := by decide +kernel
theorem certified3448 : Certified (graph core3448) (root 9) 0 5 :=
  of_native_maps core3448 DegreeTwoThreeSpectrum6259.graph DegreeTwoThreeSpectrum6260.graph
    sourceMap3448 fusedMap3448 sourceMap3448_checked fusedMap3448_checked
    DegreeTwoThreeFiniteComparisons.comparison3448
#print axioms sourceMap3448_checked
#print axioms fusedMap3448_checked
#print axioms certified3448
def sourceMap3448swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3448swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3448swap_checked : acceptsGraphIso
    (source (graph core3448) (root 9) 5 0) DegreeTwoThreeSpectrum6259.graph sourceMap3448swap=true := by decide +kernel
theorem fusedMap3448swap_checked : acceptsGraphIso
    (fused (graph core3448) (root 9) 5 0) DegreeTwoThreeSpectrum6260.graph fusedMap3448swap=true := by decide +kernel
theorem certified3448swap : Certified (graph core3448) (root 9) 5 0 :=
  of_native_maps core3448 DegreeTwoThreeSpectrum6259.graph DegreeTwoThreeSpectrum6260.graph
    sourceMap3448swap fusedMap3448swap sourceMap3448swap_checked fusedMap3448swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3448
#print axioms sourceMap3448swap_checked
#print axioms fusedMap3448swap_checked
#print axioms certified3448swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
