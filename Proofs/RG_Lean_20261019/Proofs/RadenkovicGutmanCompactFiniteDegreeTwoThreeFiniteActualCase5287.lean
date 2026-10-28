/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5287 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap5287 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,9,10,6,7,8,1,0,11,12,13,14,15] (sourceLabel 5 2 6 v)
def fusedMap5287 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 2 6 v)
theorem sourceMap5287_checked : acceptsGraphIso
    (source (graph core5287) (root 5) 2 6) DegreeTwoThreeSpectrum4544.graph sourceMap5287=true := by decide +kernel
theorem fusedMap5287_checked : acceptsGraphIso
    (fused (graph core5287) (root 5) 2 6) DegreeTwoThreeSpectrum3870.graph fusedMap5287=true := by decide +kernel
theorem certified5287 : Certified (graph core5287) (root 5) 2 6 :=
  of_native_maps core5287 DegreeTwoThreeSpectrum4544.graph DegreeTwoThreeSpectrum3870.graph
    sourceMap5287 fusedMap5287 sourceMap5287_checked fusedMap5287_checked
    DegreeTwoThreeFiniteComparisons.comparison5287
#print axioms sourceMap5287_checked
#print axioms fusedMap5287_checked
#print axioms certified5287
def sourceMap5287swap : (Vertices 5 ⊕ Fin 7 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,3,4,5,9,10,1,0,11,12,13,14,15,6,7,8] (sourceLabel 5 6 2 v)
def fusedMap5287swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 6 2 v)
theorem sourceMap5287swap_checked : acceptsGraphIso
    (source (graph core5287) (root 5) 6 2) DegreeTwoThreeSpectrum4544.graph sourceMap5287swap=true := by decide +kernel
theorem fusedMap5287swap_checked : acceptsGraphIso
    (fused (graph core5287) (root 5) 6 2) DegreeTwoThreeSpectrum3870.graph fusedMap5287swap=true := by decide +kernel
theorem certified5287swap : Certified (graph core5287) (root 5) 6 2 :=
  of_native_maps core5287 DegreeTwoThreeSpectrum4544.graph DegreeTwoThreeSpectrum3870.graph
    sourceMap5287swap fusedMap5287swap sourceMap5287swap_checked fusedMap5287swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5287
#print axioms sourceMap5287swap_checked
#print axioms fusedMap5287swap_checked
#print axioms certified5287swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
