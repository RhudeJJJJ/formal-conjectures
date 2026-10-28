/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5355 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap5355 : (Vertices 4 ⊕ Fin 4 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,6,7,8,9,2,3,4,5,0,10,11,12,13,14] (sourceLabel 4 3 5 v)
def fusedMap5355 : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14] (fusedLabel 4 3 5 v)
theorem sourceMap5355_checked : acceptsGraphIso
    (source (graph core5355) (root 4) 3 5) DegreeTwoThreeSpectrum2967.graph sourceMap5355=true := by decide +kernel
theorem fusedMap5355_checked : acceptsGraphIso
    (fused (graph core5355) (root 4) 3 5) DegreeTwoThreeSpectrum2327.graph fusedMap5355=true := by decide +kernel
theorem certified5355 : Certified (graph core5355) (root 4) 3 5 :=
  of_native_maps core5355 DegreeTwoThreeSpectrum2967.graph DegreeTwoThreeSpectrum2327.graph
    sourceMap5355 fusedMap5355 sourceMap5355_checked fusedMap5355_checked
    DegreeTwoThreeFiniteComparisons.comparison5355
#print axioms sourceMap5355_checked
#print axioms fusedMap5355_checked
#print axioms certified5355
def sourceMap5355swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,6,7,8,9,0,10,11,12,13,14,2,3,4,5] (sourceLabel 4 5 3 v)
def fusedMap5355swap : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14] (fusedLabel 4 5 3 v)
theorem sourceMap5355swap_checked : acceptsGraphIso
    (source (graph core5355) (root 4) 5 3) DegreeTwoThreeSpectrum2967.graph sourceMap5355swap=true := by decide +kernel
theorem fusedMap5355swap_checked : acceptsGraphIso
    (fused (graph core5355) (root 4) 5 3) DegreeTwoThreeSpectrum2327.graph fusedMap5355swap=true := by decide +kernel
theorem certified5355swap : Certified (graph core5355) (root 4) 5 3 :=
  of_native_maps core5355 DegreeTwoThreeSpectrum2967.graph DegreeTwoThreeSpectrum2327.graph
    sourceMap5355swap fusedMap5355swap sourceMap5355swap_checked fusedMap5355swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5355
#print axioms sourceMap5355swap_checked
#print axioms fusedMap5355swap_checked
#print axioms certified5355swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
