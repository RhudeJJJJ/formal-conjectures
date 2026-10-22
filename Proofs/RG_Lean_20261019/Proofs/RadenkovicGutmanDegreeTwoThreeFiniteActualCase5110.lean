/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5110 : Family 7 := level7.get ⟨84,by decide⟩
def sourceMap5110 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,10,11,7,8,9,0,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5110 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5110_checked : acceptsGraphIso
    (source (graph core5110) (root 7) 2 4) DegreeTwoThreeSpectrum4803.graph sourceMap5110=true := by decide +kernel
theorem fusedMap5110_checked : acceptsGraphIso
    (fused (graph core5110) (root 7) 2 4) DegreeTwoThreeSpectrum3987.graph fusedMap5110=true := by decide +kernel
theorem certified5110 : Certified (graph core5110) (root 7) 2 4 :=
  of_native_maps core5110 DegreeTwoThreeSpectrum4803.graph DegreeTwoThreeSpectrum3987.graph
    sourceMap5110 fusedMap5110 sourceMap5110_checked fusedMap5110_checked
    DegreeTwoThreeFiniteComparisons.comparison5110
#print axioms sourceMap5110_checked
#print axioms fusedMap5110_checked
#print axioms certified5110
def sourceMap5110swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,10,11,0,12,13,14,15,7,8,9] (sourceLabel 7 4 2 v)
def fusedMap5110swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5110swap_checked : acceptsGraphIso
    (source (graph core5110) (root 7) 4 2) DegreeTwoThreeSpectrum4803.graph sourceMap5110swap=true := by decide +kernel
theorem fusedMap5110swap_checked : acceptsGraphIso
    (fused (graph core5110) (root 7) 4 2) DegreeTwoThreeSpectrum3987.graph fusedMap5110swap=true := by decide +kernel
theorem certified5110swap : Certified (graph core5110) (root 7) 4 2 :=
  of_native_maps core5110 DegreeTwoThreeSpectrum4803.graph DegreeTwoThreeSpectrum3987.graph
    sourceMap5110swap fusedMap5110swap sourceMap5110swap_checked fusedMap5110swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5110
#print axioms sourceMap5110swap_checked
#print axioms fusedMap5110swap_checked
#print axioms certified5110swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
