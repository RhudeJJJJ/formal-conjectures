/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5223 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap5223 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,8,9,5,6,7,0,10,11,12,13,14] (sourceLabel 5 2 5 v)
def fusedMap5223 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 2 5 v)
theorem sourceMap5223_checked : acceptsGraphIso
    (source (graph core5223) (root 5) 2 5) DegreeTwoThreeSpectrum2815.graph sourceMap5223=true := by decide +kernel
theorem fusedMap5223_checked : acceptsGraphIso
    (fused (graph core5223) (root 5) 2 5) DegreeTwoThreeSpectrum2387.graph fusedMap5223=true := by decide +kernel
theorem certified5223 : Certified (graph core5223) (root 5) 2 5 :=
  of_native_maps core5223 DegreeTwoThreeSpectrum2815.graph DegreeTwoThreeSpectrum2387.graph
    sourceMap5223 fusedMap5223 sourceMap5223_checked fusedMap5223_checked
    DegreeTwoThreeFiniteComparisons.comparison5223
#print axioms sourceMap5223_checked
#print axioms fusedMap5223_checked
#print axioms certified5223
def sourceMap5223swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,2,3,4,8,9,0,10,11,12,13,14,5,6,7] (sourceLabel 5 5 2 v)
def fusedMap5223swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 5 2 v)
theorem sourceMap5223swap_checked : acceptsGraphIso
    (source (graph core5223) (root 5) 5 2) DegreeTwoThreeSpectrum2815.graph sourceMap5223swap=true := by decide +kernel
theorem fusedMap5223swap_checked : acceptsGraphIso
    (fused (graph core5223) (root 5) 5 2) DegreeTwoThreeSpectrum2387.graph fusedMap5223swap=true := by decide +kernel
theorem certified5223swap : Certified (graph core5223) (root 5) 5 2 :=
  of_native_maps core5223 DegreeTwoThreeSpectrum2815.graph DegreeTwoThreeSpectrum2387.graph
    sourceMap5223swap fusedMap5223swap sourceMap5223swap_checked fusedMap5223swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5223
#print axioms sourceMap5223swap_checked
#print axioms fusedMap5223swap_checked
#print axioms certified5223swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
