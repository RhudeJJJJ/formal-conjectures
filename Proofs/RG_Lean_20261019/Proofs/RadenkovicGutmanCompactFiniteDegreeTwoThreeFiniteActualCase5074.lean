/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5074 : Family 6 := level6.get ⟨28,by decide⟩
def sourceMap5074 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,10,7,8,9,0,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap5074 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap5074_checked : acceptsGraphIso
    (source (graph core5074) (root 6) 2 4) DegreeTwoThreeSpectrum3422.graph sourceMap5074=true := by decide +kernel
theorem fusedMap5074_checked : acceptsGraphIso
    (fused (graph core5074) (root 6) 2 4) DegreeTwoThreeSpectrum2350.graph fusedMap5074=true := by decide +kernel
theorem certified5074 : Certified (graph core5074) (root 6) 2 4 :=
  of_native_maps core5074 DegreeTwoThreeSpectrum3422.graph DegreeTwoThreeSpectrum2350.graph
    sourceMap5074 fusedMap5074 sourceMap5074_checked fusedMap5074_checked
    DegreeTwoThreeFiniteComparisons.comparison5074
#print axioms sourceMap5074_checked
#print axioms fusedMap5074_checked
#print axioms certified5074
def sourceMap5074swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,10,0,11,12,13,14,7,8,9] (sourceLabel 6 4 2 v)
def fusedMap5074swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap5074swap_checked : acceptsGraphIso
    (source (graph core5074) (root 6) 4 2) DegreeTwoThreeSpectrum3422.graph sourceMap5074swap=true := by decide +kernel
theorem fusedMap5074swap_checked : acceptsGraphIso
    (fused (graph core5074) (root 6) 4 2) DegreeTwoThreeSpectrum2350.graph fusedMap5074swap=true := by decide +kernel
theorem certified5074swap : Certified (graph core5074) (root 6) 4 2 :=
  of_native_maps core5074 DegreeTwoThreeSpectrum3422.graph DegreeTwoThreeSpectrum2350.graph
    sourceMap5074swap fusedMap5074swap sourceMap5074swap_checked fusedMap5074swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5074
#print axioms sourceMap5074swap_checked
#print axioms fusedMap5074swap_checked
#print axioms certified5074swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
