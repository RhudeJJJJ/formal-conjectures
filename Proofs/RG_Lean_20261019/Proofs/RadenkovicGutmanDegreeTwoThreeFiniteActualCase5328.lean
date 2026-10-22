/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5328 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap5328 : (Vertices 4 ⊕ Fin 4 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,5,6,7,8,1,2,3,4,9,10,11,12,13] (sourceLabel 4 3 4 v)
def fusedMap5328 : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 3 4 v)
theorem sourceMap5328_checked : acceptsGraphIso
    (source (graph core5328) (root 4) 3 4) DegreeTwoThreeSpectrum1909.graph sourceMap5328=true := by decide +kernel
theorem fusedMap5328_checked : acceptsGraphIso
    (fused (graph core5328) (root 4) 3 4) DegreeTwoThreeSpectrum1710.graph fusedMap5328=true := by decide +kernel
theorem certified5328 : Certified (graph core5328) (root 4) 3 4 :=
  of_native_maps core5328 DegreeTwoThreeSpectrum1909.graph DegreeTwoThreeSpectrum1710.graph
    sourceMap5328 fusedMap5328 sourceMap5328_checked fusedMap5328_checked
    DegreeTwoThreeFiniteComparisons.comparison5328
#print axioms sourceMap5328_checked
#print axioms fusedMap5328_checked
#print axioms certified5328
def sourceMap5328swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,5,6,7,8,9,10,11,12,13,1,2,3,4] (sourceLabel 4 4 3 v)
def fusedMap5328swap : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 4 3 v)
theorem sourceMap5328swap_checked : acceptsGraphIso
    (source (graph core5328) (root 4) 4 3) DegreeTwoThreeSpectrum1909.graph sourceMap5328swap=true := by decide +kernel
theorem fusedMap5328swap_checked : acceptsGraphIso
    (fused (graph core5328) (root 4) 4 3) DegreeTwoThreeSpectrum1710.graph fusedMap5328swap=true := by decide +kernel
theorem certified5328swap : Certified (graph core5328) (root 4) 4 3 :=
  of_native_maps core5328 DegreeTwoThreeSpectrum1909.graph DegreeTwoThreeSpectrum1710.graph
    sourceMap5328swap fusedMap5328swap sourceMap5328swap_checked fusedMap5328swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5328
#print axioms sourceMap5328swap_checked
#print axioms fusedMap5328swap_checked
#print axioms certified5328swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
