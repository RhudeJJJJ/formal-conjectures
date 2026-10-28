/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5399 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap5399 : (Vertices 3 ⊕ Fin 5 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,6,7,8,1,2,3,4,5,9,10,11,12,13,14] (sourceLabel 3 4 5 v)
def fusedMap5399 : (Vertices 3 ⊕ Fin 11) → Fin 15 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12,13,14] (fusedLabel 3 4 5 v)
theorem sourceMap5399_checked : acceptsGraphIso
    (source (graph core5399) (root 3) 4 5) DegreeTwoThreeSpectrum2430.graph sourceMap5399=true := by decide +kernel
theorem fusedMap5399_checked : acceptsGraphIso
    (fused (graph core5399) (root 3) 4 5) DegreeTwoThreeSpectrum2310.graph fusedMap5399=true := by decide +kernel
theorem certified5399 : Certified (graph core5399) (root 3) 4 5 :=
  of_native_maps core5399 DegreeTwoThreeSpectrum2430.graph DegreeTwoThreeSpectrum2310.graph
    sourceMap5399 fusedMap5399 sourceMap5399_checked fusedMap5399_checked
    DegreeTwoThreeFiniteComparisons.comparison5399
#print axioms sourceMap5399_checked
#print axioms fusedMap5399_checked
#print axioms certified5399
def sourceMap5399swap : (Vertices 3 ⊕ Fin 6 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,6,7,8,9,10,11,12,13,14,1,2,3,4,5] (sourceLabel 3 5 4 v)
def fusedMap5399swap : (Vertices 3 ⊕ Fin 11) → Fin 15 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12,13,14] (fusedLabel 3 5 4 v)
theorem sourceMap5399swap_checked : acceptsGraphIso
    (source (graph core5399) (root 3) 5 4) DegreeTwoThreeSpectrum2430.graph sourceMap5399swap=true := by decide +kernel
theorem fusedMap5399swap_checked : acceptsGraphIso
    (fused (graph core5399) (root 3) 5 4) DegreeTwoThreeSpectrum2310.graph fusedMap5399swap=true := by decide +kernel
theorem certified5399swap : Certified (graph core5399) (root 3) 5 4 :=
  of_native_maps core5399 DegreeTwoThreeSpectrum2430.graph DegreeTwoThreeSpectrum2310.graph
    sourceMap5399swap fusedMap5399swap sourceMap5399swap_checked fusedMap5399swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5399
#print axioms sourceMap5399swap_checked
#print axioms fusedMap5399swap_checked
#print axioms certified5399swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
