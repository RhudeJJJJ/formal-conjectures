/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5103 : Family 7 := level7.get ⟨68,by decide⟩
def sourceMap5103 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,10,11,7,8,9,0,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5103 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5103_checked : acceptsGraphIso
    (source (graph core5103) (root 7) 2 4) DegreeTwoThreeSpectrum4711.graph sourceMap5103=true := by decide +kernel
theorem fusedMap5103_checked : acceptsGraphIso
    (fused (graph core5103) (root 7) 2 4) DegreeTwoThreeSpectrum3903.graph fusedMap5103=true := by decide +kernel
theorem certified5103 : Certified (graph core5103) (root 7) 2 4 :=
  of_native_maps core5103 DegreeTwoThreeSpectrum4711.graph DegreeTwoThreeSpectrum3903.graph
    sourceMap5103 fusedMap5103 sourceMap5103_checked fusedMap5103_checked
    DegreeTwoThreeFiniteComparisons.comparison5103
#print axioms sourceMap5103_checked
#print axioms fusedMap5103_checked
#print axioms certified5103
def sourceMap5103swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,10,11,0,12,13,14,15,7,8,9] (sourceLabel 7 4 2 v)
def fusedMap5103swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5103swap_checked : acceptsGraphIso
    (source (graph core5103) (root 7) 4 2) DegreeTwoThreeSpectrum4711.graph sourceMap5103swap=true := by decide +kernel
theorem fusedMap5103swap_checked : acceptsGraphIso
    (fused (graph core5103) (root 7) 4 2) DegreeTwoThreeSpectrum3903.graph fusedMap5103swap=true := by decide +kernel
theorem certified5103swap : Certified (graph core5103) (root 7) 4 2 :=
  of_native_maps core5103 DegreeTwoThreeSpectrum4711.graph DegreeTwoThreeSpectrum3903.graph
    sourceMap5103swap fusedMap5103swap sourceMap5103swap_checked fusedMap5103swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5103
#print axioms sourceMap5103swap_checked
#print axioms fusedMap5103swap_checked
#print axioms certified5103swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
