/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5360 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap5360 : (Vertices 5 ⊕ Fin 4 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,6,7,8,9,10,2,3,4,5,0,11,12,13,14,15] (sourceLabel 5 3 5 v)
def fusedMap5360 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 3 5 v)
theorem sourceMap5360_checked : acceptsGraphIso
    (source (graph core5360) (root 5) 3 5) DegreeTwoThreeSpectrum4642.graph sourceMap5360=true := by decide +kernel
theorem fusedMap5360_checked : acceptsGraphIso
    (fused (graph core5360) (root 5) 3 5) DegreeTwoThreeSpectrum3870.graph fusedMap5360=true := by decide +kernel
theorem certified5360 : Certified (graph core5360) (root 5) 3 5 :=
  of_native_maps core5360 DegreeTwoThreeSpectrum4642.graph DegreeTwoThreeSpectrum3870.graph
    sourceMap5360 fusedMap5360 sourceMap5360_checked fusedMap5360_checked
    DegreeTwoThreeFiniteComparisons.comparison5360
#print axioms sourceMap5360_checked
#print axioms fusedMap5360_checked
#print axioms certified5360
def sourceMap5360swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 4) → Fin 16 :=
  fun v => ![1,6,7,8,9,10,0,11,12,13,14,15,2,3,4,5] (sourceLabel 5 5 3 v)
def fusedMap5360swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 5 3 v)
theorem sourceMap5360swap_checked : acceptsGraphIso
    (source (graph core5360) (root 5) 5 3) DegreeTwoThreeSpectrum4642.graph sourceMap5360swap=true := by decide +kernel
theorem fusedMap5360swap_checked : acceptsGraphIso
    (fused (graph core5360) (root 5) 5 3) DegreeTwoThreeSpectrum3870.graph fusedMap5360swap=true := by decide +kernel
theorem certified5360swap : Certified (graph core5360) (root 5) 5 3 :=
  of_native_maps core5360 DegreeTwoThreeSpectrum4642.graph DegreeTwoThreeSpectrum3870.graph
    sourceMap5360swap fusedMap5360swap sourceMap5360swap_checked fusedMap5360swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5360
#print axioms sourceMap5360swap_checked
#print axioms fusedMap5360swap_checked
#print axioms certified5360swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
