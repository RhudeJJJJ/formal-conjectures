/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5220 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap5220 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,9,6,7,8,0,10,11,12,13,14] (sourceLabel 5 2 5 v)
def fusedMap5220 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13,14] (fusedLabel 5 2 5 v)
theorem sourceMap5220_checked : acceptsGraphIso
    (source (graph core5220) (root 5) 2 5) DegreeTwoThreeSpectrum2956.graph sourceMap5220=true := by decide +kernel
theorem fusedMap5220_checked : acceptsGraphIso
    (fused (graph core5220) (root 5) 2 5) DegreeTwoThreeSpectrum2312.graph fusedMap5220=true := by decide +kernel
theorem certified5220 : Certified (graph core5220) (root 5) 2 5 :=
  of_native_maps core5220 DegreeTwoThreeSpectrum2956.graph DegreeTwoThreeSpectrum2312.graph
    sourceMap5220 fusedMap5220 sourceMap5220_checked fusedMap5220_checked
    DegreeTwoThreeFiniteComparisons.comparison5220
#print axioms sourceMap5220_checked
#print axioms fusedMap5220_checked
#print axioms certified5220
def sourceMap5220swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,2,3,4,5,9,0,10,11,12,13,14,6,7,8] (sourceLabel 5 5 2 v)
def fusedMap5220swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13,14] (fusedLabel 5 5 2 v)
theorem sourceMap5220swap_checked : acceptsGraphIso
    (source (graph core5220) (root 5) 5 2) DegreeTwoThreeSpectrum2956.graph sourceMap5220swap=true := by decide +kernel
theorem fusedMap5220swap_checked : acceptsGraphIso
    (fused (graph core5220) (root 5) 5 2) DegreeTwoThreeSpectrum2312.graph fusedMap5220swap=true := by decide +kernel
theorem certified5220swap : Certified (graph core5220) (root 5) 5 2 :=
  of_native_maps core5220 DegreeTwoThreeSpectrum2956.graph DegreeTwoThreeSpectrum2312.graph
    sourceMap5220swap fusedMap5220swap sourceMap5220swap_checked fusedMap5220swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5220
#print axioms sourceMap5220swap_checked
#print axioms fusedMap5220swap_checked
#print axioms certified5220swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
