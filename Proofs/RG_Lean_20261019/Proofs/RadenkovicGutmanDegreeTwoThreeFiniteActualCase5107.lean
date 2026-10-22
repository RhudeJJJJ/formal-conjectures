/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5107 : Family 7 := level7.get ⟨77,by decide⟩
def sourceMap5107 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5107 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5107_checked : acceptsGraphIso
    (source (graph core5107) (root 7) 2 4) DegreeTwoThreeSpectrum4765.graph sourceMap5107=true := by decide +kernel
theorem fusedMap5107_checked : acceptsGraphIso
    (fused (graph core5107) (root 7) 2 4) DegreeTwoThreeSpectrum3941.graph fusedMap5107=true := by decide +kernel
theorem certified5107 : Certified (graph core5107) (root 7) 2 4 :=
  of_native_maps core5107 DegreeTwoThreeSpectrum4765.graph DegreeTwoThreeSpectrum3941.graph
    sourceMap5107 fusedMap5107 sourceMap5107_checked fusedMap5107_checked
    DegreeTwoThreeFiniteComparisons.comparison5107
#print axioms sourceMap5107_checked
#print axioms fusedMap5107_checked
#print axioms certified5107
def sourceMap5107swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,12,13,14,15,9,10,11] (sourceLabel 7 4 2 v)
def fusedMap5107swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5107swap_checked : acceptsGraphIso
    (source (graph core5107) (root 7) 4 2) DegreeTwoThreeSpectrum4765.graph sourceMap5107swap=true := by decide +kernel
theorem fusedMap5107swap_checked : acceptsGraphIso
    (fused (graph core5107) (root 7) 4 2) DegreeTwoThreeSpectrum3941.graph fusedMap5107swap=true := by decide +kernel
theorem certified5107swap : Certified (graph core5107) (root 7) 4 2 :=
  of_native_maps core5107 DegreeTwoThreeSpectrum4765.graph DegreeTwoThreeSpectrum3941.graph
    sourceMap5107swap fusedMap5107swap sourceMap5107swap_checked fusedMap5107swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5107
#print axioms sourceMap5107swap_checked
#print axioms fusedMap5107swap_checked
#print axioms certified5107swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
