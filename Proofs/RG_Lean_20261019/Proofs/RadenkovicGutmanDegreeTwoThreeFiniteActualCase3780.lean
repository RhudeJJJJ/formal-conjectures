/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3780 : Family 6 := level6.get ⟨24,by decide⟩
def sourceMap3780 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,9,7,8,0,10,11,12,13] (sourceLabel 6 1 4 v)
def fusedMap3780 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 1 4 v)
theorem sourceMap3780_checked : acceptsGraphIso
    (source (graph core3780) (root 6) 1 4) DegreeTwoThreeSpectrum2023.graph sourceMap3780=true := by decide +kernel
theorem fusedMap3780_checked : acceptsGraphIso
    (fused (graph core3780) (root 6) 1 4) DegreeTwoThreeSpectrum1768.graph fusedMap3780=true := by decide +kernel
theorem certified3780 : Certified (graph core3780) (root 6) 1 4 :=
  of_native_maps core3780 DegreeTwoThreeSpectrum2023.graph DegreeTwoThreeSpectrum1768.graph
    sourceMap3780 fusedMap3780 sourceMap3780_checked fusedMap3780_checked
    DegreeTwoThreeFiniteComparisons.comparison3780
#print axioms sourceMap3780_checked
#print axioms fusedMap3780_checked
#print axioms certified3780
def sourceMap3780swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 2) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,9,0,10,11,12,13,7,8] (sourceLabel 6 4 1 v)
def fusedMap3780swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 4 1 v)
theorem sourceMap3780swap_checked : acceptsGraphIso
    (source (graph core3780) (root 6) 4 1) DegreeTwoThreeSpectrum2023.graph sourceMap3780swap=true := by decide +kernel
theorem fusedMap3780swap_checked : acceptsGraphIso
    (fused (graph core3780) (root 6) 4 1) DegreeTwoThreeSpectrum1768.graph fusedMap3780swap=true := by decide +kernel
theorem certified3780swap : Certified (graph core3780) (root 6) 4 1 :=
  of_native_maps core3780 DegreeTwoThreeSpectrum2023.graph DegreeTwoThreeSpectrum1768.graph
    sourceMap3780swap fusedMap3780swap sourceMap3780swap_checked fusedMap3780swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3780
#print axioms sourceMap3780swap_checked
#print axioms fusedMap3780swap_checked
#print axioms certified3780swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
