/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5210 : Family 8 := level8.get ⟨257,by decide⟩
def sourceMap5210 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,8,9,10,11,12,5,6,7,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5210 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5210_checked : acceptsGraphIso
    (source (graph core5210) (root 8) 2 4) DegreeTwoThreeSpectrum7486.graph sourceMap5210=true := by decide +kernel
theorem fusedMap5210_checked : acceptsGraphIso
    (fused (graph core5210) (root 8) 2 4) DegreeTwoThreeSpectrum5671.graph fusedMap5210=true := by decide +kernel
theorem certified5210 : Certified (graph core5210) (root 8) 2 4 :=
  of_native_maps core5210 DegreeTwoThreeSpectrum7486.graph DegreeTwoThreeSpectrum5671.graph
    sourceMap5210 fusedMap5210 sourceMap5210_checked fusedMap5210_checked
    DegreeTwoThreeFiniteComparisons.comparison5210
#print axioms sourceMap5210_checked
#print axioms fusedMap5210_checked
#print axioms certified5210
def sourceMap5210swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,8,9,10,11,12,0,13,14,15,16,5,6,7] (sourceLabel 8 4 2 v)
def fusedMap5210swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5210swap_checked : acceptsGraphIso
    (source (graph core5210) (root 8) 4 2) DegreeTwoThreeSpectrum7486.graph sourceMap5210swap=true := by decide +kernel
theorem fusedMap5210swap_checked : acceptsGraphIso
    (fused (graph core5210) (root 8) 4 2) DegreeTwoThreeSpectrum5671.graph fusedMap5210swap=true := by decide +kernel
theorem certified5210swap : Certified (graph core5210) (root 8) 4 2 :=
  of_native_maps core5210 DegreeTwoThreeSpectrum7486.graph DegreeTwoThreeSpectrum5671.graph
    sourceMap5210swap fusedMap5210swap sourceMap5210swap_checked fusedMap5210swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5210
#print axioms sourceMap5210swap_checked
#print axioms fusedMap5210swap_checked
#print axioms certified5210swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
