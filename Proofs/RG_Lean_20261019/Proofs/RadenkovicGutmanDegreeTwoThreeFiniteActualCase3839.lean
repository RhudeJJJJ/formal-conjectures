/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3839 : Family 8 := level8.get ⟨56,by decide⟩
def sourceMap3839 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,13,14,8,9,10,11,12] (sourceLabel 8 1 4 v)
def fusedMap3839 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3839_checked : acceptsGraphIso
    (source (graph core3839) (root 8) 1 4) DegreeTwoThreeSpectrum4438.graph sourceMap3839=true := by decide +kernel
theorem fusedMap3839_checked : acceptsGraphIso
    (fused (graph core3839) (root 8) 1 4) DegreeTwoThreeSpectrum3998.graph fusedMap3839=true := by decide +kernel
theorem certified3839 : Certified (graph core3839) (root 8) 1 4 :=
  of_native_maps core3839 DegreeTwoThreeSpectrum4438.graph DegreeTwoThreeSpectrum3998.graph
    sourceMap3839 fusedMap3839 sourceMap3839_checked fusedMap3839_checked
    DegreeTwoThreeFiniteComparisons.comparison3839
#print axioms sourceMap3839_checked
#print axioms fusedMap3839_checked
#print axioms certified3839
def sourceMap3839swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,8,9,10,11,12,13,14] (sourceLabel 8 4 1 v)
def fusedMap3839swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3839swap_checked : acceptsGraphIso
    (source (graph core3839) (root 8) 4 1) DegreeTwoThreeSpectrum4438.graph sourceMap3839swap=true := by decide +kernel
theorem fusedMap3839swap_checked : acceptsGraphIso
    (fused (graph core3839) (root 8) 4 1) DegreeTwoThreeSpectrum3998.graph fusedMap3839swap=true := by decide +kernel
theorem certified3839swap : Certified (graph core3839) (root 8) 4 1 :=
  of_native_maps core3839 DegreeTwoThreeSpectrum4438.graph DegreeTwoThreeSpectrum3998.graph
    sourceMap3839swap fusedMap3839swap sourceMap3839swap_checked fusedMap3839swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3839
#print axioms sourceMap3839swap_checked
#print axioms fusedMap3839swap_checked
#print axioms certified3839swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
