/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3939 : Family 6 := level6.get ⟨21,by decide⟩
def sourceMap3939 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,9,7,8,0,10,11,12,13,14] (sourceLabel 6 1 5 v)
def fusedMap3939 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 1 5 v)
theorem sourceMap3939_checked : acceptsGraphIso
    (source (graph core3939) (root 6) 1 5) DegreeTwoThreeSpectrum2475.graph sourceMap3939=true := by decide +kernel
theorem fusedMap3939_checked : acceptsGraphIso
    (fused (graph core3939) (root 6) 1 5) DegreeTwoThreeSpectrum2316.graph fusedMap3939=true := by decide +kernel
theorem certified3939 : Certified (graph core3939) (root 6) 1 5 :=
  of_native_maps core3939 DegreeTwoThreeSpectrum2475.graph DegreeTwoThreeSpectrum2316.graph
    sourceMap3939 fusedMap3939 sourceMap3939_checked fusedMap3939_checked
    DegreeTwoThreeFiniteComparisons.comparison3939
#print axioms sourceMap3939_checked
#print axioms fusedMap3939_checked
#print axioms certified3939
def sourceMap3939swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,9,0,10,11,12,13,14,7,8] (sourceLabel 6 5 1 v)
def fusedMap3939swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 5 1 v)
theorem sourceMap3939swap_checked : acceptsGraphIso
    (source (graph core3939) (root 6) 5 1) DegreeTwoThreeSpectrum2475.graph sourceMap3939swap=true := by decide +kernel
theorem fusedMap3939swap_checked : acceptsGraphIso
    (fused (graph core3939) (root 6) 5 1) DegreeTwoThreeSpectrum2316.graph fusedMap3939swap=true := by decide +kernel
theorem certified3939swap : Certified (graph core3939) (root 6) 5 1 :=
  of_native_maps core3939 DegreeTwoThreeSpectrum2475.graph DegreeTwoThreeSpectrum2316.graph
    sourceMap3939swap fusedMap3939swap sourceMap3939swap_checked fusedMap3939swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3939
#print axioms sourceMap3939swap_checked
#print axioms fusedMap3939swap_checked
#print axioms certified3939swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
