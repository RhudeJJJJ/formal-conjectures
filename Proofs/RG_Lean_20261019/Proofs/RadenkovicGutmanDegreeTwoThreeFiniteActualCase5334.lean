/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5334 : Family 5 := level5.get ⟨14,by decide⟩
def sourceMap5334 : (Vertices 5 ⊕ Fin 4 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,5,6,7,8,9,1,2,3,4,10,11,12,13,14] (sourceLabel 5 3 4 v)
def fusedMap5334 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 3 4 v)
theorem sourceMap5334_checked : acceptsGraphIso
    (source (graph core5334) (root 5) 3 4) DegreeTwoThreeSpectrum2962.graph sourceMap5334=true := by decide +kernel
theorem fusedMap5334_checked : acceptsGraphIso
    (fused (graph core5334) (root 5) 3 4) DegreeTwoThreeSpectrum2315.graph fusedMap5334=true := by decide +kernel
theorem certified5334 : Certified (graph core5334) (root 5) 3 4 :=
  of_native_maps core5334 DegreeTwoThreeSpectrum2962.graph DegreeTwoThreeSpectrum2315.graph
    sourceMap5334 fusedMap5334 sourceMap5334_checked fusedMap5334_checked
    DegreeTwoThreeFiniteComparisons.comparison5334
#print axioms sourceMap5334_checked
#print axioms fusedMap5334_checked
#print axioms certified5334
def sourceMap5334swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,5,6,7,8,9,10,11,12,13,14,1,2,3,4] (sourceLabel 5 4 3 v)
def fusedMap5334swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 4 3 v)
theorem sourceMap5334swap_checked : acceptsGraphIso
    (source (graph core5334) (root 5) 4 3) DegreeTwoThreeSpectrum2962.graph sourceMap5334swap=true := by decide +kernel
theorem fusedMap5334swap_checked : acceptsGraphIso
    (fused (graph core5334) (root 5) 4 3) DegreeTwoThreeSpectrum2315.graph fusedMap5334swap=true := by decide +kernel
theorem certified5334swap : Certified (graph core5334) (root 5) 4 3 :=
  of_native_maps core5334 DegreeTwoThreeSpectrum2962.graph DegreeTwoThreeSpectrum2315.graph
    sourceMap5334swap fusedMap5334swap sourceMap5334swap_checked fusedMap5334swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5334
#print axioms sourceMap5334swap_checked
#print axioms fusedMap5334swap_checked
#print axioms certified5334swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
