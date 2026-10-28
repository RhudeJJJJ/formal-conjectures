/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5410 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap5410 : (Vertices 3 ⊕ Fin 5 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,7,8,9,2,3,4,5,6,0,10,11,12,13,14,15] (sourceLabel 3 4 6 v)
def fusedMap5410 : (Vertices 3 ⊕ Fin 12) → Fin 16 :=
  fun v => ![5,6,7,8,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 3 4 6 v)
theorem sourceMap5410_checked : acceptsGraphIso
    (source (graph core5410) (root 3) 4 6) DegreeTwoThreeSpectrum4160.graph sourceMap5410=true := by decide +kernel
theorem fusedMap5410_checked : acceptsGraphIso
    (fused (graph core5410) (root 3) 4 6) DegreeTwoThreeSpectrum3869.graph fusedMap5410=true := by decide +kernel
theorem certified5410 : Certified (graph core5410) (root 3) 4 6 :=
  of_native_maps core5410 DegreeTwoThreeSpectrum4160.graph DegreeTwoThreeSpectrum3869.graph
    sourceMap5410 fusedMap5410 sourceMap5410_checked fusedMap5410_checked
    DegreeTwoThreeFiniteComparisons.comparison5410
#print axioms sourceMap5410_checked
#print axioms fusedMap5410_checked
#print axioms certified5410
def sourceMap5410swap : (Vertices 3 ⊕ Fin 7 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,7,8,9,0,10,11,12,13,14,15,2,3,4,5,6] (sourceLabel 3 6 4 v)
def fusedMap5410swap : (Vertices 3 ⊕ Fin 12) → Fin 16 :=
  fun v => ![5,6,7,8,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 3 6 4 v)
theorem sourceMap5410swap_checked : acceptsGraphIso
    (source (graph core5410) (root 3) 6 4) DegreeTwoThreeSpectrum4160.graph sourceMap5410swap=true := by decide +kernel
theorem fusedMap5410swap_checked : acceptsGraphIso
    (fused (graph core5410) (root 3) 6 4) DegreeTwoThreeSpectrum3869.graph fusedMap5410swap=true := by decide +kernel
theorem certified5410swap : Certified (graph core5410) (root 3) 6 4 :=
  of_native_maps core5410 DegreeTwoThreeSpectrum4160.graph DegreeTwoThreeSpectrum3869.graph
    sourceMap5410swap fusedMap5410swap sourceMap5410swap_checked fusedMap5410swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5410
#print axioms sourceMap5410swap_checked
#print axioms fusedMap5410swap_checked
#print axioms certified5410swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
