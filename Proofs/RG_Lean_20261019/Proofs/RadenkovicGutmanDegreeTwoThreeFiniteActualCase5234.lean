/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5234 : Family 6 := level6.get ⟨28,by decide⟩
def sourceMap5234 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,10,7,8,9,0,11,12,13,14,15] (sourceLabel 6 2 5 v)
def fusedMap5234 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 2 5 v)
theorem sourceMap5234_checked : acceptsGraphIso
    (source (graph core5234) (root 6) 2 5) DegreeTwoThreeSpectrum4415.graph sourceMap5234=true := by decide +kernel
theorem fusedMap5234_checked : acceptsGraphIso
    (fused (graph core5234) (root 6) 2 5) DegreeTwoThreeSpectrum3991.graph fusedMap5234=true := by decide +kernel
theorem certified5234 : Certified (graph core5234) (root 6) 2 5 :=
  of_native_maps core5234 DegreeTwoThreeSpectrum4415.graph DegreeTwoThreeSpectrum3991.graph
    sourceMap5234 fusedMap5234 sourceMap5234_checked fusedMap5234_checked
    DegreeTwoThreeFiniteComparisons.comparison5234
#print axioms sourceMap5234_checked
#print axioms fusedMap5234_checked
#print axioms certified5234
def sourceMap5234swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,10,0,11,12,13,14,15,7,8,9] (sourceLabel 6 5 2 v)
def fusedMap5234swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 5 2 v)
theorem sourceMap5234swap_checked : acceptsGraphIso
    (source (graph core5234) (root 6) 5 2) DegreeTwoThreeSpectrum4415.graph sourceMap5234swap=true := by decide +kernel
theorem fusedMap5234swap_checked : acceptsGraphIso
    (fused (graph core5234) (root 6) 5 2) DegreeTwoThreeSpectrum3991.graph fusedMap5234swap=true := by decide +kernel
theorem certified5234swap : Certified (graph core5234) (root 6) 5 2 :=
  of_native_maps core5234 DegreeTwoThreeSpectrum4415.graph DegreeTwoThreeSpectrum3991.graph
    sourceMap5234swap fusedMap5234swap sourceMap5234swap_checked fusedMap5234swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5234
#print axioms sourceMap5234swap_checked
#print axioms fusedMap5234swap_checked
#print axioms certified5234swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
