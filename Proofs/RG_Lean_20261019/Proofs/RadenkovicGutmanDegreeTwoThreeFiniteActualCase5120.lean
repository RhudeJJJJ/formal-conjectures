/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5120 : Family 8 := level8.get ⟨13,by decide⟩
def sourceMap5120 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,16,13,14,15,8,9,10,11,12] (sourceLabel 8 2 4 v)
def fusedMap5120 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5120_checked : acceptsGraphIso
    (source (graph core5120) (root 8) 2 4) DegreeTwoThreeSpectrum5414.graph sourceMap5120=true := by decide +kernel
theorem fusedMap5120_checked : acceptsGraphIso
    (fused (graph core5120) (root 8) 2 4) DegreeTwoThreeSpectrum5002.graph fusedMap5120=true := by decide +kernel
theorem certified5120 : Certified (graph core5120) (root 8) 2 4 :=
  of_native_maps core5120 DegreeTwoThreeSpectrum5414.graph DegreeTwoThreeSpectrum5002.graph
    sourceMap5120 fusedMap5120 sourceMap5120_checked fusedMap5120_checked
    DegreeTwoThreeFiniteComparisons.comparison5120
#print axioms sourceMap5120_checked
#print axioms fusedMap5120_checked
#print axioms certified5120
def sourceMap5120swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,16,8,9,10,11,12,13,14,15] (sourceLabel 8 4 2 v)
def fusedMap5120swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5120swap_checked : acceptsGraphIso
    (source (graph core5120) (root 8) 4 2) DegreeTwoThreeSpectrum5414.graph sourceMap5120swap=true := by decide +kernel
theorem fusedMap5120swap_checked : acceptsGraphIso
    (fused (graph core5120) (root 8) 4 2) DegreeTwoThreeSpectrum5002.graph fusedMap5120swap=true := by decide +kernel
theorem certified5120swap : Certified (graph core5120) (root 8) 4 2 :=
  of_native_maps core5120 DegreeTwoThreeSpectrum5414.graph DegreeTwoThreeSpectrum5002.graph
    sourceMap5120swap fusedMap5120swap sourceMap5120swap_checked fusedMap5120swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5120
#print axioms sourceMap5120swap_checked
#print axioms fusedMap5120swap_checked
#print axioms certified5120swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
