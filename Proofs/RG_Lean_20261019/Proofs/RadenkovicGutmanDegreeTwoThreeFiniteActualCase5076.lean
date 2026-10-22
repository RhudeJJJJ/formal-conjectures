/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5076 : Family 6 := level6.get ⟨31,by decide⟩
def sourceMap5076 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,9,10,6,7,8,0,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap5076 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap5076_checked : acceptsGraphIso
    (source (graph core5076) (root 6) 2 4) DegreeTwoThreeSpectrum3532.graph sourceMap5076=true := by decide +kernel
theorem fusedMap5076_checked : acceptsGraphIso
    (fused (graph core5076) (root 6) 2 4) DegreeTwoThreeSpectrum2360.graph fusedMap5076=true := by decide +kernel
theorem certified5076 : Certified (graph core5076) (root 6) 2 4 :=
  of_native_maps core5076 DegreeTwoThreeSpectrum3532.graph DegreeTwoThreeSpectrum2360.graph
    sourceMap5076 fusedMap5076 sourceMap5076_checked fusedMap5076_checked
    DegreeTwoThreeFiniteComparisons.comparison5076
#print axioms sourceMap5076_checked
#print axioms fusedMap5076_checked
#print axioms certified5076
def sourceMap5076swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,2,3,4,5,9,10,0,11,12,13,14,6,7,8] (sourceLabel 6 4 2 v)
def fusedMap5076swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap5076swap_checked : acceptsGraphIso
    (source (graph core5076) (root 6) 4 2) DegreeTwoThreeSpectrum3532.graph sourceMap5076swap=true := by decide +kernel
theorem fusedMap5076swap_checked : acceptsGraphIso
    (fused (graph core5076) (root 6) 4 2) DegreeTwoThreeSpectrum2360.graph fusedMap5076swap=true := by decide +kernel
theorem certified5076swap : Certified (graph core5076) (root 6) 4 2 :=
  of_native_maps core5076 DegreeTwoThreeSpectrum3532.graph DegreeTwoThreeSpectrum2360.graph
    sourceMap5076swap fusedMap5076swap sourceMap5076swap_checked fusedMap5076swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5076
#print axioms sourceMap5076swap_checked
#print axioms fusedMap5076swap_checked
#print axioms certified5076swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
