/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5348 : Family 6 := level6.get ⟨34,by decide⟩
def sourceMap5348 : (Vertices 6 ⊕ Fin 4 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,5,6,7,8,9,10,1,2,3,4,11,12,13,14,15] (sourceLabel 6 3 4 v)
def fusedMap5348 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 3 4 v)
theorem sourceMap5348_checked : acceptsGraphIso
    (source (graph core5348) (root 6) 3 4) DegreeTwoThreeSpectrum4641.graph sourceMap5348=true := by decide +kernel
theorem fusedMap5348_checked : acceptsGraphIso
    (fused (graph core5348) (root 6) 3 4) DegreeTwoThreeSpectrum4067.graph fusedMap5348=true := by decide +kernel
theorem certified5348 : Certified (graph core5348) (root 6) 3 4 :=
  of_native_maps core5348 DegreeTwoThreeSpectrum4641.graph DegreeTwoThreeSpectrum4067.graph
    sourceMap5348 fusedMap5348 sourceMap5348_checked fusedMap5348_checked
    DegreeTwoThreeFiniteComparisons.comparison5348
#print axioms sourceMap5348_checked
#print axioms fusedMap5348_checked
#print axioms certified5348
def sourceMap5348swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 4) → Fin 16 :=
  fun v => ![0,5,6,7,8,9,10,11,12,13,14,15,1,2,3,4] (sourceLabel 6 4 3 v)
def fusedMap5348swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 4 3 v)
theorem sourceMap5348swap_checked : acceptsGraphIso
    (source (graph core5348) (root 6) 4 3) DegreeTwoThreeSpectrum4641.graph sourceMap5348swap=true := by decide +kernel
theorem fusedMap5348swap_checked : acceptsGraphIso
    (fused (graph core5348) (root 6) 4 3) DegreeTwoThreeSpectrum4067.graph fusedMap5348swap=true := by decide +kernel
theorem certified5348swap : Certified (graph core5348) (root 6) 4 3 :=
  of_native_maps core5348 DegreeTwoThreeSpectrum4641.graph DegreeTwoThreeSpectrum4067.graph
    sourceMap5348swap fusedMap5348swap sourceMap5348swap_checked fusedMap5348swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5348
#print axioms sourceMap5348swap_checked
#print axioms fusedMap5348swap_checked
#print axioms certified5348swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
