/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5106 : Family 7 := level7.get ⟨75,by decide⟩
def sourceMap5106 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,10,11,7,8,9,0,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5106 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5106_checked : acceptsGraphIso
    (source (graph core5106) (root 7) 2 4) DegreeTwoThreeSpectrum4747.graph sourceMap5106=true := by decide +kernel
theorem fusedMap5106_checked : acceptsGraphIso
    (fused (graph core5106) (root 7) 2 4) DegreeTwoThreeSpectrum3927.graph fusedMap5106=true := by decide +kernel
theorem certified5106 : Certified (graph core5106) (root 7) 2 4 :=
  of_native_maps core5106 DegreeTwoThreeSpectrum4747.graph DegreeTwoThreeSpectrum3927.graph
    sourceMap5106 fusedMap5106 sourceMap5106_checked fusedMap5106_checked
    DegreeTwoThreeFiniteComparisons.comparison5106
#print axioms sourceMap5106_checked
#print axioms fusedMap5106_checked
#print axioms certified5106
def sourceMap5106swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,10,11,0,12,13,14,15,7,8,9] (sourceLabel 7 4 2 v)
def fusedMap5106swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5106swap_checked : acceptsGraphIso
    (source (graph core5106) (root 7) 4 2) DegreeTwoThreeSpectrum4747.graph sourceMap5106swap=true := by decide +kernel
theorem fusedMap5106swap_checked : acceptsGraphIso
    (fused (graph core5106) (root 7) 4 2) DegreeTwoThreeSpectrum3927.graph fusedMap5106swap=true := by decide +kernel
theorem certified5106swap : Certified (graph core5106) (root 7) 4 2 :=
  of_native_maps core5106 DegreeTwoThreeSpectrum4747.graph DegreeTwoThreeSpectrum3927.graph
    sourceMap5106swap fusedMap5106swap sourceMap5106swap_checked fusedMap5106swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5106
#print axioms sourceMap5106swap_checked
#print axioms fusedMap5106swap_checked
#print axioms certified5106swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
