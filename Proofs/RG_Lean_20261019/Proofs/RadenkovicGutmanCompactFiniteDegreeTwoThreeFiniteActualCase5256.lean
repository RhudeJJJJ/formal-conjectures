/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5256 : Family 7 := level7.get ⟨53,by decide⟩
def sourceMap5256 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,8,9,10,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5256 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5256_checked : acceptsGraphIso
    (source (graph core5256) (root 7) 2 5) DegreeTwoThreeSpectrum6922.graph sourceMap5256=true := by decide +kernel
theorem fusedMap5256_checked : acceptsGraphIso
    (fused (graph core5256) (root 7) 2 5) DegreeTwoThreeSpectrum5051.graph fusedMap5256=true := by decide +kernel
theorem certified5256 : Certified (graph core5256) (root 7) 2 5 :=
  of_native_maps core5256 DegreeTwoThreeSpectrum6922.graph DegreeTwoThreeSpectrum5051.graph
    sourceMap5256 fusedMap5256 sourceMap5256_checked fusedMap5256_checked
    DegreeTwoThreeFiniteComparisons.comparison5256
#print axioms sourceMap5256_checked
#print axioms fusedMap5256_checked
#print axioms certified5256
def sourceMap5256swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,0,12,13,14,15,16,8,9,10] (sourceLabel 7 5 2 v)
def fusedMap5256swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5256swap_checked : acceptsGraphIso
    (source (graph core5256) (root 7) 5 2) DegreeTwoThreeSpectrum6922.graph sourceMap5256swap=true := by decide +kernel
theorem fusedMap5256swap_checked : acceptsGraphIso
    (fused (graph core5256) (root 7) 5 2) DegreeTwoThreeSpectrum5051.graph fusedMap5256swap=true := by decide +kernel
theorem certified5256swap : Certified (graph core5256) (root 7) 5 2 :=
  of_native_maps core5256 DegreeTwoThreeSpectrum6922.graph DegreeTwoThreeSpectrum5051.graph
    sourceMap5256swap fusedMap5256swap sourceMap5256swap_checked fusedMap5256swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5256
#print axioms sourceMap5256swap_checked
#print axioms fusedMap5256swap_checked
#print axioms certified5256swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
