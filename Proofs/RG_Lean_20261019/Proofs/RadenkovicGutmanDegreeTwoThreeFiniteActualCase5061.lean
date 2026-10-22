/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5061 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap5061 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,9,6,7,8,0,10,11,12,13] (sourceLabel 5 2 4 v)
def fusedMap5061 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 2 4 v)
theorem sourceMap5061_checked : acceptsGraphIso
    (source (graph core5061) (root 5) 2 4) DegreeTwoThreeSpectrum2042.graph sourceMap5061=true := by decide +kernel
theorem fusedMap5061_checked : acceptsGraphIso
    (fused (graph core5061) (root 5) 2 4) DegreeTwoThreeSpectrum1711.graph fusedMap5061=true := by decide +kernel
theorem certified5061 : Certified (graph core5061) (root 5) 2 4 :=
  of_native_maps core5061 DegreeTwoThreeSpectrum2042.graph DegreeTwoThreeSpectrum1711.graph
    sourceMap5061 fusedMap5061 sourceMap5061_checked fusedMap5061_checked
    DegreeTwoThreeFiniteComparisons.comparison5061
#print axioms sourceMap5061_checked
#print axioms fusedMap5061_checked
#print axioms certified5061
def sourceMap5061swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,2,3,4,5,9,0,10,11,12,13,6,7,8] (sourceLabel 5 4 2 v)
def fusedMap5061swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 4 2 v)
theorem sourceMap5061swap_checked : acceptsGraphIso
    (source (graph core5061) (root 5) 4 2) DegreeTwoThreeSpectrum2042.graph sourceMap5061swap=true := by decide +kernel
theorem fusedMap5061swap_checked : acceptsGraphIso
    (fused (graph core5061) (root 5) 4 2) DegreeTwoThreeSpectrum1711.graph fusedMap5061swap=true := by decide +kernel
theorem certified5061swap : Certified (graph core5061) (root 5) 4 2 :=
  of_native_maps core5061 DegreeTwoThreeSpectrum2042.graph DegreeTwoThreeSpectrum1711.graph
    sourceMap5061swap fusedMap5061swap sourceMap5061swap_checked fusedMap5061swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5061
#print axioms sourceMap5061swap_checked
#print axioms fusedMap5061swap_checked
#print axioms certified5061swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
