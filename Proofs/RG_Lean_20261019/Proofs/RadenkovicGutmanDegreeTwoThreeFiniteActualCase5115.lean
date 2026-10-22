/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5115 : Family 7 := level7.get ⟨95,by decide⟩
def sourceMap5115 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,8,9,10,11,5,6,7,0,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5115 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5115_checked : acceptsGraphIso
    (source (graph core5115) (root 7) 2 4) DegreeTwoThreeSpectrum4868.graph sourceMap5115=true := by decide +kernel
theorem fusedMap5115_checked : acceptsGraphIso
    (fused (graph core5115) (root 7) 2 4) DegreeTwoThreeSpectrum4063.graph fusedMap5115=true := by decide +kernel
theorem certified5115 : Certified (graph core5115) (root 7) 2 4 :=
  of_native_maps core5115 DegreeTwoThreeSpectrum4868.graph DegreeTwoThreeSpectrum4063.graph
    sourceMap5115 fusedMap5115 sourceMap5115_checked fusedMap5115_checked
    DegreeTwoThreeFiniteComparisons.comparison5115
#print axioms sourceMap5115_checked
#print axioms fusedMap5115_checked
#print axioms certified5115
def sourceMap5115swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,8,9,10,11,0,12,13,14,15,5,6,7] (sourceLabel 7 4 2 v)
def fusedMap5115swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5115swap_checked : acceptsGraphIso
    (source (graph core5115) (root 7) 4 2) DegreeTwoThreeSpectrum4868.graph sourceMap5115swap=true := by decide +kernel
theorem fusedMap5115swap_checked : acceptsGraphIso
    (fused (graph core5115) (root 7) 4 2) DegreeTwoThreeSpectrum4063.graph fusedMap5115swap=true := by decide +kernel
theorem certified5115swap : Certified (graph core5115) (root 7) 4 2 :=
  of_native_maps core5115 DegreeTwoThreeSpectrum4868.graph DegreeTwoThreeSpectrum4063.graph
    sourceMap5115swap fusedMap5115swap sourceMap5115swap_checked fusedMap5115swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5115
#print axioms sourceMap5115swap_checked
#print axioms fusedMap5115swap_checked
#print axioms certified5115swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
