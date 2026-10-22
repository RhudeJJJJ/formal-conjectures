/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5327 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap5327 : (Vertices 4 ⊕ Fin 4 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,5,6,7,8,1,2,3,4,9,10,11,12,13] (sourceLabel 4 3 4 v)
def fusedMap5327 : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 3 4 v)
theorem sourceMap5327_checked : acceptsGraphIso
    (source (graph core5327) (root 4) 3 4) DegreeTwoThreeSpectrum1905.graph sourceMap5327=true := by decide +kernel
theorem fusedMap5327_checked : acceptsGraphIso
    (fused (graph core5327) (root 4) 3 4) DegreeTwoThreeSpectrum1728.graph fusedMap5327=true := by decide +kernel
theorem certified5327 : Certified (graph core5327) (root 4) 3 4 :=
  of_native_maps core5327 DegreeTwoThreeSpectrum1905.graph DegreeTwoThreeSpectrum1728.graph
    sourceMap5327 fusedMap5327 sourceMap5327_checked fusedMap5327_checked
    DegreeTwoThreeFiniteComparisons.comparison5327
#print axioms sourceMap5327_checked
#print axioms fusedMap5327_checked
#print axioms certified5327
def sourceMap5327swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,5,6,7,8,9,10,11,12,13,1,2,3,4] (sourceLabel 4 4 3 v)
def fusedMap5327swap : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 4 3 v)
theorem sourceMap5327swap_checked : acceptsGraphIso
    (source (graph core5327) (root 4) 4 3) DegreeTwoThreeSpectrum1905.graph sourceMap5327swap=true := by decide +kernel
theorem fusedMap5327swap_checked : acceptsGraphIso
    (fused (graph core5327) (root 4) 4 3) DegreeTwoThreeSpectrum1728.graph fusedMap5327swap=true := by decide +kernel
theorem certified5327swap : Certified (graph core5327) (root 4) 4 3 :=
  of_native_maps core5327 DegreeTwoThreeSpectrum1905.graph DegreeTwoThreeSpectrum1728.graph
    sourceMap5327swap fusedMap5327swap sourceMap5327swap_checked fusedMap5327swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5327
#print axioms sourceMap5327swap_checked
#print axioms fusedMap5327swap_checked
#print axioms certified5327swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
