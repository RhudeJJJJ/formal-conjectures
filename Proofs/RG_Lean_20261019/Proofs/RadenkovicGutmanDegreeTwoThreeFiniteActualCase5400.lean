/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5400 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap5400 : (Vertices 4 ⊕ Fin 5 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,6,7,8,9,1,2,3,4,5,10,11,12,13,14,15] (sourceLabel 4 4 5 v)
def fusedMap5400 : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 4 5 v)
theorem sourceMap5400_checked : acceptsGraphIso
    (source (graph core5400) (root 4) 4 5) DegreeTwoThreeSpectrum4153.graph sourceMap5400=true := by decide +kernel
theorem fusedMap5400_checked : acceptsGraphIso
    (fused (graph core5400) (root 4) 4 5) DegreeTwoThreeSpectrum3876.graph fusedMap5400=true := by decide +kernel
theorem certified5400 : Certified (graph core5400) (root 4) 4 5 :=
  of_native_maps core5400 DegreeTwoThreeSpectrum4153.graph DegreeTwoThreeSpectrum3876.graph
    sourceMap5400 fusedMap5400 sourceMap5400_checked fusedMap5400_checked
    DegreeTwoThreeFiniteComparisons.comparison5400
#print axioms sourceMap5400_checked
#print axioms fusedMap5400_checked
#print axioms certified5400
def sourceMap5400swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,6,7,8,9,10,11,12,13,14,15,1,2,3,4,5] (sourceLabel 4 5 4 v)
def fusedMap5400swap : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 5 4 v)
theorem sourceMap5400swap_checked : acceptsGraphIso
    (source (graph core5400) (root 4) 5 4) DegreeTwoThreeSpectrum4153.graph sourceMap5400swap=true := by decide +kernel
theorem fusedMap5400swap_checked : acceptsGraphIso
    (fused (graph core5400) (root 4) 5 4) DegreeTwoThreeSpectrum3876.graph fusedMap5400swap=true := by decide +kernel
theorem certified5400swap : Certified (graph core5400) (root 4) 5 4 :=
  of_native_maps core5400 DegreeTwoThreeSpectrum4153.graph DegreeTwoThreeSpectrum3876.graph
    sourceMap5400swap fusedMap5400swap sourceMap5400swap_checked fusedMap5400swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5400
#print axioms sourceMap5400swap_checked
#print axioms fusedMap5400swap_checked
#print axioms certified5400swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
