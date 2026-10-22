/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3940 : Family 6 := level6.get ⟨24,by decide⟩
def sourceMap3940 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,9,7,8,0,10,11,12,13,14] (sourceLabel 6 1 5 v)
def fusedMap3940 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 1 5 v)
theorem sourceMap3940_checked : acceptsGraphIso
    (source (graph core3940) (root 6) 1 5) DegreeTwoThreeSpectrum2534.graph sourceMap3940=true := by decide +kernel
theorem fusedMap3940_checked : acceptsGraphIso
    (fused (graph core3940) (root 6) 1 5) DegreeTwoThreeSpectrum2323.graph fusedMap3940=true := by decide +kernel
theorem certified3940 : Certified (graph core3940) (root 6) 1 5 :=
  of_native_maps core3940 DegreeTwoThreeSpectrum2534.graph DegreeTwoThreeSpectrum2323.graph
    sourceMap3940 fusedMap3940 sourceMap3940_checked fusedMap3940_checked
    DegreeTwoThreeFiniteComparisons.comparison3940
#print axioms sourceMap3940_checked
#print axioms fusedMap3940_checked
#print axioms certified3940
def sourceMap3940swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,9,0,10,11,12,13,14,7,8] (sourceLabel 6 5 1 v)
def fusedMap3940swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 5 1 v)
theorem sourceMap3940swap_checked : acceptsGraphIso
    (source (graph core3940) (root 6) 5 1) DegreeTwoThreeSpectrum2534.graph sourceMap3940swap=true := by decide +kernel
theorem fusedMap3940swap_checked : acceptsGraphIso
    (fused (graph core3940) (root 6) 5 1) DegreeTwoThreeSpectrum2323.graph fusedMap3940swap=true := by decide +kernel
theorem certified3940swap : Certified (graph core3940) (root 6) 5 1 :=
  of_native_maps core3940 DegreeTwoThreeSpectrum2534.graph DegreeTwoThreeSpectrum2323.graph
    sourceMap3940swap fusedMap3940swap sourceMap3940swap_checked fusedMap3940swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3940
#print axioms sourceMap3940swap_checked
#print axioms fusedMap3940swap_checked
#print axioms certified3940swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
