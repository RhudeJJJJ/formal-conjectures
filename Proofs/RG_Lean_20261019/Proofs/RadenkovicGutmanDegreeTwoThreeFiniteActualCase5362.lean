/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5362 : Family 5 := level5.get ⟨15,by decide⟩
def sourceMap5362 : (Vertices 5 ⊕ Fin 4 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,6,7,8,9,10,2,3,4,5,0,11,12,13,14,15] (sourceLabel 5 3 5 v)
def fusedMap5362 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15] (fusedLabel 5 3 5 v)
theorem sourceMap5362_checked : acceptsGraphIso
    (source (graph core5362) (root 5) 3 5) DegreeTwoThreeSpectrum4649.graph sourceMap5362=true := by decide +kernel
theorem fusedMap5362_checked : acceptsGraphIso
    (fused (graph core5362) (root 5) 3 5) DegreeTwoThreeSpectrum3922.graph fusedMap5362=true := by decide +kernel
theorem certified5362 : Certified (graph core5362) (root 5) 3 5 :=
  of_native_maps core5362 DegreeTwoThreeSpectrum4649.graph DegreeTwoThreeSpectrum3922.graph
    sourceMap5362 fusedMap5362 sourceMap5362_checked fusedMap5362_checked
    DegreeTwoThreeFiniteComparisons.comparison5362
#print axioms sourceMap5362_checked
#print axioms fusedMap5362_checked
#print axioms certified5362
def sourceMap5362swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 4) → Fin 16 :=
  fun v => ![1,6,7,8,9,10,0,11,12,13,14,15,2,3,4,5] (sourceLabel 5 5 3 v)
def fusedMap5362swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15] (fusedLabel 5 5 3 v)
theorem sourceMap5362swap_checked : acceptsGraphIso
    (source (graph core5362) (root 5) 5 3) DegreeTwoThreeSpectrum4649.graph sourceMap5362swap=true := by decide +kernel
theorem fusedMap5362swap_checked : acceptsGraphIso
    (fused (graph core5362) (root 5) 5 3) DegreeTwoThreeSpectrum3922.graph fusedMap5362swap=true := by decide +kernel
theorem certified5362swap : Certified (graph core5362) (root 5) 5 3 :=
  of_native_maps core5362 DegreeTwoThreeSpectrum4649.graph DegreeTwoThreeSpectrum3922.graph
    sourceMap5362swap fusedMap5362swap sourceMap5362swap_checked fusedMap5362swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5362
#print axioms sourceMap5362swap_checked
#print axioms fusedMap5362swap_checked
#print axioms certified5362swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
