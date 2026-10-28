/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5109 : Family 7 := level7.get ⟨83,by decide⟩
def sourceMap5109 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,11,8,9,10,0,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5109 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5109_checked : acceptsGraphIso
    (source (graph core5109) (root 7) 2 4) DegreeTwoThreeSpectrum4795.graph sourceMap5109=true := by decide +kernel
theorem fusedMap5109_checked : acceptsGraphIso
    (fused (graph core5109) (root 7) 2 4) DegreeTwoThreeSpectrum3983.graph fusedMap5109=true := by decide +kernel
theorem certified5109 : Certified (graph core5109) (root 7) 2 4 :=
  of_native_maps core5109 DegreeTwoThreeSpectrum4795.graph DegreeTwoThreeSpectrum3983.graph
    sourceMap5109 fusedMap5109 sourceMap5109_checked fusedMap5109_checked
    DegreeTwoThreeFiniteComparisons.comparison5109
#print axioms sourceMap5109_checked
#print axioms fusedMap5109_checked
#print axioms certified5109
def sourceMap5109swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,11,0,12,13,14,15,8,9,10] (sourceLabel 7 4 2 v)
def fusedMap5109swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5109swap_checked : acceptsGraphIso
    (source (graph core5109) (root 7) 4 2) DegreeTwoThreeSpectrum4795.graph sourceMap5109swap=true := by decide +kernel
theorem fusedMap5109swap_checked : acceptsGraphIso
    (fused (graph core5109) (root 7) 4 2) DegreeTwoThreeSpectrum3983.graph fusedMap5109swap=true := by decide +kernel
theorem certified5109swap : Certified (graph core5109) (root 7) 4 2 :=
  of_native_maps core5109 DegreeTwoThreeSpectrum4795.graph DegreeTwoThreeSpectrum3983.graph
    sourceMap5109swap fusedMap5109swap sourceMap5109swap_checked fusedMap5109swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5109
#print axioms sourceMap5109swap_checked
#print axioms fusedMap5109swap_checked
#print axioms certified5109swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
