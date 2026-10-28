/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5363 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap5363 : (Vertices 2 ⊕ Fin 4 ⊕ Fin 7) → Fin 14 :=
  fun v => ![1,6,7,2,3,4,5,0,8,9,10,11,12,13] (sourceLabel 2 3 6 v)
def fusedMap5363 : (Vertices 2 ⊕ Fin 11) → Fin 14 :=
  fun v => ![5,6,7,4,3,2,1,0,8,9,10,11,12,13] (fusedLabel 2 3 6 v)
theorem sourceMap5363_checked : acceptsGraphIso
    (source (graph core5363) (root 2) 3 6) DegreeTwoThreeSpectrum1730.graph sourceMap5363=true := by decide +kernel
theorem fusedMap5363_checked : acceptsGraphIso
    (fused (graph core5363) (root 2) 3 6) DegreeTwoThreeSpectrum1715.graph fusedMap5363=true := by decide +kernel
theorem certified5363 : Certified (graph core5363) (root 2) 3 6 :=
  of_native_maps core5363 DegreeTwoThreeSpectrum1730.graph DegreeTwoThreeSpectrum1715.graph
    sourceMap5363 fusedMap5363 sourceMap5363_checked fusedMap5363_checked
    DegreeTwoThreeFiniteComparisons.comparison5363
#print axioms sourceMap5363_checked
#print axioms fusedMap5363_checked
#print axioms certified5363
def sourceMap5363swap : (Vertices 2 ⊕ Fin 7 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,6,7,0,8,9,10,11,12,13,2,3,4,5] (sourceLabel 2 6 3 v)
def fusedMap5363swap : (Vertices 2 ⊕ Fin 11) → Fin 14 :=
  fun v => ![5,6,7,4,3,2,1,0,8,9,10,11,12,13] (fusedLabel 2 6 3 v)
theorem sourceMap5363swap_checked : acceptsGraphIso
    (source (graph core5363) (root 2) 6 3) DegreeTwoThreeSpectrum1730.graph sourceMap5363swap=true := by decide +kernel
theorem fusedMap5363swap_checked : acceptsGraphIso
    (fused (graph core5363) (root 2) 6 3) DegreeTwoThreeSpectrum1715.graph fusedMap5363swap=true := by decide +kernel
theorem certified5363swap : Certified (graph core5363) (root 2) 6 3 :=
  of_native_maps core5363 DegreeTwoThreeSpectrum1730.graph DegreeTwoThreeSpectrum1715.graph
    sourceMap5363swap fusedMap5363swap sourceMap5363swap_checked fusedMap5363swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5363
#print axioms sourceMap5363swap_checked
#print axioms fusedMap5363swap_checked
#print axioms certified5363swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
