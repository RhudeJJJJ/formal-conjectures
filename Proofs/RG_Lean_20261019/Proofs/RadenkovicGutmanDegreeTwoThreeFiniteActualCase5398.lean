/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5398 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap5398 : (Vertices 2 ⊕ Fin 5 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,6,7,1,2,3,4,5,8,9,10,11,12,13] (sourceLabel 2 4 5 v)
def fusedMap5398 : (Vertices 2 ⊕ Fin 11) → Fin 14 :=
  fun v => ![5,6,7,4,3,2,1,0,8,9,10,11,12,13] (fusedLabel 2 4 5 v)
theorem sourceMap5398_checked : acceptsGraphIso
    (source (graph core5398) (root 2) 4 5) DegreeTwoThreeSpectrum1736.graph sourceMap5398=true := by decide +kernel
theorem fusedMap5398_checked : acceptsGraphIso
    (fused (graph core5398) (root 2) 4 5) DegreeTwoThreeSpectrum1715.graph fusedMap5398=true := by decide +kernel
theorem certified5398 : Certified (graph core5398) (root 2) 4 5 :=
  of_native_maps core5398 DegreeTwoThreeSpectrum1736.graph DegreeTwoThreeSpectrum1715.graph
    sourceMap5398 fusedMap5398 sourceMap5398_checked fusedMap5398_checked
    DegreeTwoThreeFiniteComparisons.comparison5398
#print axioms sourceMap5398_checked
#print axioms fusedMap5398_checked
#print axioms certified5398
def sourceMap5398swap : (Vertices 2 ⊕ Fin 6 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,6,7,8,9,10,11,12,13,1,2,3,4,5] (sourceLabel 2 5 4 v)
def fusedMap5398swap : (Vertices 2 ⊕ Fin 11) → Fin 14 :=
  fun v => ![5,6,7,4,3,2,1,0,8,9,10,11,12,13] (fusedLabel 2 5 4 v)
theorem sourceMap5398swap_checked : acceptsGraphIso
    (source (graph core5398) (root 2) 5 4) DegreeTwoThreeSpectrum1736.graph sourceMap5398swap=true := by decide +kernel
theorem fusedMap5398swap_checked : acceptsGraphIso
    (fused (graph core5398) (root 2) 5 4) DegreeTwoThreeSpectrum1715.graph fusedMap5398swap=true := by decide +kernel
theorem certified5398swap : Certified (graph core5398) (root 2) 5 4 :=
  of_native_maps core5398 DegreeTwoThreeSpectrum1736.graph DegreeTwoThreeSpectrum1715.graph
    sourceMap5398swap fusedMap5398swap sourceMap5398swap_checked fusedMap5398swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5398
#print axioms sourceMap5398swap_checked
#print axioms fusedMap5398swap_checked
#print axioms certified5398swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
