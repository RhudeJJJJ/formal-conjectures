/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3858 : Family 8 := level8.get ⟨114,by decide⟩
def sourceMap3858 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,8,9,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3858 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3858_checked : acceptsGraphIso
    (source (graph core3858) (root 8) 1 4) DegreeTwoThreeSpectrum4299.graph sourceMap3858=true := by decide +kernel
theorem fusedMap3858_checked : acceptsGraphIso
    (fused (graph core3858) (root 8) 1 4) DegreeTwoThreeSpectrum3924.graph fusedMap3858=true := by decide +kernel
theorem certified3858 : Certified (graph core3858) (root 8) 1 4 :=
  of_native_maps core3858 DegreeTwoThreeSpectrum4299.graph DegreeTwoThreeSpectrum3924.graph
    sourceMap3858 fusedMap3858 sourceMap3858_checked fusedMap3858_checked
    DegreeTwoThreeFiniteComparisons.comparison3858
#print axioms sourceMap3858_checked
#print axioms fusedMap3858_checked
#print axioms certified3858
def sourceMap3858swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,15,8,9] (sourceLabel 8 4 1 v)
def fusedMap3858swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3858swap_checked : acceptsGraphIso
    (source (graph core3858) (root 8) 4 1) DegreeTwoThreeSpectrum4299.graph sourceMap3858swap=true := by decide +kernel
theorem fusedMap3858swap_checked : acceptsGraphIso
    (fused (graph core3858) (root 8) 4 1) DegreeTwoThreeSpectrum3924.graph fusedMap3858swap=true := by decide +kernel
theorem certified3858swap : Certified (graph core3858) (root 8) 4 1 :=
  of_native_maps core3858 DegreeTwoThreeSpectrum4299.graph DegreeTwoThreeSpectrum3924.graph
    sourceMap3858swap fusedMap3858swap sourceMap3858swap_checked fusedMap3858swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3858
#print axioms sourceMap3858swap_checked
#print axioms fusedMap3858swap_checked
#print axioms certified3858swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
