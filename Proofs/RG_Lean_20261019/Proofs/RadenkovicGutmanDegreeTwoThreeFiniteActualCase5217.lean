/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5217 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap5217 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,8,5,6,7,0,9,10,11,12,13] (sourceLabel 4 2 5 v)
def fusedMap5217 : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 2 5 v)
theorem sourceMap5217_checked : acceptsGraphIso
    (source (graph core5217) (root 4) 2 5) DegreeTwoThreeSpectrum1859.graph sourceMap5217=true := by decide +kernel
theorem fusedMap5217_checked : acceptsGraphIso
    (fused (graph core5217) (root 4) 2 5) DegreeTwoThreeSpectrum1728.graph fusedMap5217=true := by decide +kernel
theorem certified5217 : Certified (graph core5217) (root 4) 2 5 :=
  of_native_maps core5217 DegreeTwoThreeSpectrum1859.graph DegreeTwoThreeSpectrum1728.graph
    sourceMap5217 fusedMap5217 sourceMap5217_checked fusedMap5217_checked
    DegreeTwoThreeFiniteComparisons.comparison5217
#print axioms sourceMap5217_checked
#print axioms fusedMap5217_checked
#print axioms certified5217
def sourceMap5217swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,2,3,4,8,0,9,10,11,12,13,5,6,7] (sourceLabel 4 5 2 v)
def fusedMap5217swap : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 5 2 v)
theorem sourceMap5217swap_checked : acceptsGraphIso
    (source (graph core5217) (root 4) 5 2) DegreeTwoThreeSpectrum1859.graph sourceMap5217swap=true := by decide +kernel
theorem fusedMap5217swap_checked : acceptsGraphIso
    (fused (graph core5217) (root 4) 5 2) DegreeTwoThreeSpectrum1728.graph fusedMap5217swap=true := by decide +kernel
theorem certified5217swap : Certified (graph core5217) (root 4) 5 2 :=
  of_native_maps core5217 DegreeTwoThreeSpectrum1859.graph DegreeTwoThreeSpectrum1728.graph
    sourceMap5217swap fusedMap5217swap sourceMap5217swap_checked fusedMap5217swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5217
#print axioms sourceMap5217swap_checked
#print axioms fusedMap5217swap_checked
#print axioms certified5217swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
