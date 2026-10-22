/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3850 : Family 8 := level8.get ⟨89,by decide⟩
def sourceMap3850 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11] (sourceLabel 8 1 4 v)
def fusedMap3850 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3850_checked : acceptsGraphIso
    (source (graph core3850) (root 8) 1 4) DegreeTwoThreeSpectrum4657.graph sourceMap3850=true := by decide +kernel
theorem fusedMap3850_checked : acceptsGraphIso
    (fused (graph core3850) (root 8) 1 4) DegreeTwoThreeSpectrum4142.graph fusedMap3850=true := by decide +kernel
theorem certified3850 : Certified (graph core3850) (root 8) 1 4 :=
  of_native_maps core3850 DegreeTwoThreeSpectrum4657.graph DegreeTwoThreeSpectrum4142.graph
    sourceMap3850 fusedMap3850 sourceMap3850_checked fusedMap3850_checked
    DegreeTwoThreeFiniteComparisons.comparison3850
#print axioms sourceMap3850_checked
#print axioms fusedMap3850_checked
#print axioms certified3850
def sourceMap3850swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,12,13,7,8,9,10,11,14,15] (sourceLabel 8 4 1 v)
def fusedMap3850swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3850swap_checked : acceptsGraphIso
    (source (graph core3850) (root 8) 4 1) DegreeTwoThreeSpectrum4657.graph sourceMap3850swap=true := by decide +kernel
theorem fusedMap3850swap_checked : acceptsGraphIso
    (fused (graph core3850) (root 8) 4 1) DegreeTwoThreeSpectrum4142.graph fusedMap3850swap=true := by decide +kernel
theorem certified3850swap : Certified (graph core3850) (root 8) 4 1 :=
  of_native_maps core3850 DegreeTwoThreeSpectrum4657.graph DegreeTwoThreeSpectrum4142.graph
    sourceMap3850swap fusedMap3850swap sourceMap3850swap_checked fusedMap3850swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3850
#print axioms sourceMap3850swap_checked
#print axioms fusedMap3850swap_checked
#print axioms certified3850swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
