/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5111 : Family 7 := level7.get ⟨87,by decide⟩
def sourceMap5111 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,11,8,9,10,0,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5111 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5111_checked : acceptsGraphIso
    (source (graph core5111) (root 7) 2 4) DegreeTwoThreeSpectrum4817.graph sourceMap5111=true := by decide +kernel
theorem fusedMap5111_checked : acceptsGraphIso
    (fused (graph core5111) (root 7) 2 4) DegreeTwoThreeSpectrum4001.graph fusedMap5111=true := by decide +kernel
theorem certified5111 : Certified (graph core5111) (root 7) 2 4 :=
  of_native_maps core5111 DegreeTwoThreeSpectrum4817.graph DegreeTwoThreeSpectrum4001.graph
    sourceMap5111 fusedMap5111 sourceMap5111_checked fusedMap5111_checked
    DegreeTwoThreeFiniteComparisons.comparison5111
#print axioms sourceMap5111_checked
#print axioms fusedMap5111_checked
#print axioms certified5111
def sourceMap5111swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,11,0,12,13,14,15,8,9,10] (sourceLabel 7 4 2 v)
def fusedMap5111swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5111swap_checked : acceptsGraphIso
    (source (graph core5111) (root 7) 4 2) DegreeTwoThreeSpectrum4817.graph sourceMap5111swap=true := by decide +kernel
theorem fusedMap5111swap_checked : acceptsGraphIso
    (fused (graph core5111) (root 7) 4 2) DegreeTwoThreeSpectrum4001.graph fusedMap5111swap=true := by decide +kernel
theorem certified5111swap : Certified (graph core5111) (root 7) 4 2 :=
  of_native_maps core5111 DegreeTwoThreeSpectrum4817.graph DegreeTwoThreeSpectrum4001.graph
    sourceMap5111swap fusedMap5111swap sourceMap5111swap_checked fusedMap5111swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5111
#print axioms sourceMap5111swap_checked
#print axioms fusedMap5111swap_checked
#print axioms certified5111swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
