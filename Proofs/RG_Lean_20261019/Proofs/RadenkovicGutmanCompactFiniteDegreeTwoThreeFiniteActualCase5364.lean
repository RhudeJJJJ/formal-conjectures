/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5364 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap5364 : (Vertices 3 ⊕ Fin 4 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,6,7,8,2,3,4,5,0,9,10,11,12,13,14] (sourceLabel 3 3 6 v)
def fusedMap5364 : (Vertices 3 ⊕ Fin 11) → Fin 15 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12,13,14] (fusedLabel 3 3 6 v)
theorem sourceMap5364_checked : acceptsGraphIso
    (source (graph core5364) (root 3) 3 6) DegreeTwoThreeSpectrum2410.graph sourceMap5364=true := by decide +kernel
theorem fusedMap5364_checked : acceptsGraphIso
    (fused (graph core5364) (root 3) 3 6) DegreeTwoThreeSpectrum2310.graph fusedMap5364=true := by decide +kernel
theorem certified5364 : Certified (graph core5364) (root 3) 3 6 :=
  of_native_maps core5364 DegreeTwoThreeSpectrum2410.graph DegreeTwoThreeSpectrum2310.graph
    sourceMap5364 fusedMap5364 sourceMap5364_checked fusedMap5364_checked
    DegreeTwoThreeFiniteComparisons.comparison5364
#print axioms sourceMap5364_checked
#print axioms fusedMap5364_checked
#print axioms certified5364
def sourceMap5364swap : (Vertices 3 ⊕ Fin 7 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,6,7,8,0,9,10,11,12,13,14,2,3,4,5] (sourceLabel 3 6 3 v)
def fusedMap5364swap : (Vertices 3 ⊕ Fin 11) → Fin 15 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12,13,14] (fusedLabel 3 6 3 v)
theorem sourceMap5364swap_checked : acceptsGraphIso
    (source (graph core5364) (root 3) 6 3) DegreeTwoThreeSpectrum2410.graph sourceMap5364swap=true := by decide +kernel
theorem fusedMap5364swap_checked : acceptsGraphIso
    (fused (graph core5364) (root 3) 6 3) DegreeTwoThreeSpectrum2310.graph fusedMap5364swap=true := by decide +kernel
theorem certified5364swap : Certified (graph core5364) (root 3) 6 3 :=
  of_native_maps core5364 DegreeTwoThreeSpectrum2410.graph DegreeTwoThreeSpectrum2310.graph
    sourceMap5364swap fusedMap5364swap sourceMap5364swap_checked fusedMap5364swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5364
#print axioms sourceMap5364swap_checked
#print axioms fusedMap5364swap_checked
#print axioms certified5364swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
