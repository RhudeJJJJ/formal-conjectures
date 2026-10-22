/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3935 : Family 6 := level6.get ⟨9,by decide⟩
def sourceMap3935 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,9,7,8,0,10,11,12,13,14] (sourceLabel 6 1 5 v)
def fusedMap3935 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 1 5 v)
theorem sourceMap3935_checked : acceptsGraphIso
    (source (graph core3935) (root 6) 1 5) DegreeTwoThreeSpectrum2611.graph sourceMap3935=true := by decide +kernel
theorem fusedMap3935_checked : acceptsGraphIso
    (fused (graph core3935) (root 6) 1 5) DegreeTwoThreeSpectrum2338.graph fusedMap3935=true := by decide +kernel
theorem certified3935 : Certified (graph core3935) (root 6) 1 5 :=
  of_native_maps core3935 DegreeTwoThreeSpectrum2611.graph DegreeTwoThreeSpectrum2338.graph
    sourceMap3935 fusedMap3935 sourceMap3935_checked fusedMap3935_checked
    DegreeTwoThreeFiniteComparisons.comparison3935
#print axioms sourceMap3935_checked
#print axioms fusedMap3935_checked
#print axioms certified3935
def sourceMap3935swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,9,0,10,11,12,13,14,7,8] (sourceLabel 6 5 1 v)
def fusedMap3935swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 5 1 v)
theorem sourceMap3935swap_checked : acceptsGraphIso
    (source (graph core3935) (root 6) 5 1) DegreeTwoThreeSpectrum2611.graph sourceMap3935swap=true := by decide +kernel
theorem fusedMap3935swap_checked : acceptsGraphIso
    (fused (graph core3935) (root 6) 5 1) DegreeTwoThreeSpectrum2338.graph fusedMap3935swap=true := by decide +kernel
theorem certified3935swap : Certified (graph core3935) (root 6) 5 1 :=
  of_native_maps core3935 DegreeTwoThreeSpectrum2611.graph DegreeTwoThreeSpectrum2338.graph
    sourceMap3935swap fusedMap3935swap sourceMap3935swap_checked fusedMap3935swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3935
#print axioms sourceMap3935swap_checked
#print axioms fusedMap3935swap_checked
#print axioms certified3935swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
