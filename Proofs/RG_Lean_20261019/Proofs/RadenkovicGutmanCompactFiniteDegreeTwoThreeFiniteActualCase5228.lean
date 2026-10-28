/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5228 : Family 6 := level6.get ⟨13,by decide⟩
def sourceMap5228 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,10,7,8,9,0,11,12,13,14,15] (sourceLabel 6 2 5 v)
def fusedMap5228 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 2 5 v)
theorem sourceMap5228_checked : acceptsGraphIso
    (source (graph core5228) (root 6) 2 5) DegreeTwoThreeSpectrum4523.graph sourceMap5228=true := by decide +kernel
theorem fusedMap5228_checked : acceptsGraphIso
    (fused (graph core5228) (root 6) 2 5) DegreeTwoThreeSpectrum3865.graph fusedMap5228=true := by decide +kernel
theorem certified5228 : Certified (graph core5228) (root 6) 2 5 :=
  of_native_maps core5228 DegreeTwoThreeSpectrum4523.graph DegreeTwoThreeSpectrum3865.graph
    sourceMap5228 fusedMap5228 sourceMap5228_checked fusedMap5228_checked
    DegreeTwoThreeFiniteComparisons.comparison5228
#print axioms sourceMap5228_checked
#print axioms fusedMap5228_checked
#print axioms certified5228
def sourceMap5228swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,10,0,11,12,13,14,15,7,8,9] (sourceLabel 6 5 2 v)
def fusedMap5228swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 5 2 v)
theorem sourceMap5228swap_checked : acceptsGraphIso
    (source (graph core5228) (root 6) 5 2) DegreeTwoThreeSpectrum4523.graph sourceMap5228swap=true := by decide +kernel
theorem fusedMap5228swap_checked : acceptsGraphIso
    (fused (graph core5228) (root 6) 5 2) DegreeTwoThreeSpectrum3865.graph fusedMap5228swap=true := by decide +kernel
theorem certified5228swap : Certified (graph core5228) (root 6) 5 2 :=
  of_native_maps core5228 DegreeTwoThreeSpectrum4523.graph DegreeTwoThreeSpectrum3865.graph
    sourceMap5228swap fusedMap5228swap sourceMap5228swap_checked fusedMap5228swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5228
#print axioms sourceMap5228swap_checked
#print axioms fusedMap5228swap_checked
#print axioms certified5228swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
