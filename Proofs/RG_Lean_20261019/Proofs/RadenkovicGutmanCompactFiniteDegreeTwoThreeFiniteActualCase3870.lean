/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3870 : Family 8 := level8.get ⟨146,by decide⟩
def sourceMap3870 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,8,9,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3870 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3870_checked : acceptsGraphIso
    (source (graph core3870) (root 8) 1 4) DegreeTwoThreeSpectrum4468.graph sourceMap3870=true := by decide +kernel
theorem fusedMap3870_checked : acceptsGraphIso
    (fused (graph core3870) (root 8) 1 4) DegreeTwoThreeSpectrum4006.graph fusedMap3870=true := by decide +kernel
theorem certified3870 : Certified (graph core3870) (root 8) 1 4 :=
  of_native_maps core3870 DegreeTwoThreeSpectrum4468.graph DegreeTwoThreeSpectrum4006.graph
    sourceMap3870 fusedMap3870 sourceMap3870_checked fusedMap3870_checked
    DegreeTwoThreeFiniteComparisons.comparison3870
#print axioms sourceMap3870_checked
#print axioms fusedMap3870_checked
#print axioms certified3870
def sourceMap3870swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,15,8,9] (sourceLabel 8 4 1 v)
def fusedMap3870swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3870swap_checked : acceptsGraphIso
    (source (graph core3870) (root 8) 4 1) DegreeTwoThreeSpectrum4468.graph sourceMap3870swap=true := by decide +kernel
theorem fusedMap3870swap_checked : acceptsGraphIso
    (fused (graph core3870) (root 8) 4 1) DegreeTwoThreeSpectrum4006.graph fusedMap3870swap=true := by decide +kernel
theorem certified3870swap : Certified (graph core3870) (root 8) 4 1 :=
  of_native_maps core3870 DegreeTwoThreeSpectrum4468.graph DegreeTwoThreeSpectrum4006.graph
    sourceMap3870swap fusedMap3870swap sourceMap3870swap_checked fusedMap3870swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3870
#print axioms sourceMap3870swap_checked
#print axioms fusedMap3870swap_checked
#print axioms certified3870swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
