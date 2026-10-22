/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5170 : Family 8 := level8.get ⟨165,by decide⟩
def sourceMap5170 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5170 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5170_checked : acceptsGraphIso
    (source (graph core5170) (root 8) 2 4) DegreeTwoThreeSpectrum6889.graph sourceMap5170=true := by decide +kernel
theorem fusedMap5170_checked : acceptsGraphIso
    (fused (graph core5170) (root 8) 2 4) DegreeTwoThreeSpectrum5683.graph fusedMap5170=true := by decide +kernel
theorem certified5170 : Certified (graph core5170) (root 8) 2 4 :=
  of_native_maps core5170 DegreeTwoThreeSpectrum6889.graph DegreeTwoThreeSpectrum5683.graph
    sourceMap5170 fusedMap5170 sourceMap5170_checked fusedMap5170_checked
    DegreeTwoThreeFiniteComparisons.comparison5170
#print axioms sourceMap5170_checked
#print axioms fusedMap5170_checked
#print axioms certified5170
def sourceMap5170swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5170swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5170swap_checked : acceptsGraphIso
    (source (graph core5170) (root 8) 4 2) DegreeTwoThreeSpectrum6889.graph sourceMap5170swap=true := by decide +kernel
theorem fusedMap5170swap_checked : acceptsGraphIso
    (fused (graph core5170) (root 8) 4 2) DegreeTwoThreeSpectrum5683.graph fusedMap5170swap=true := by decide +kernel
theorem certified5170swap : Certified (graph core5170) (root 8) 4 2 :=
  of_native_maps core5170 DegreeTwoThreeSpectrum6889.graph DegreeTwoThreeSpectrum5683.graph
    sourceMap5170swap fusedMap5170swap sourceMap5170swap_checked fusedMap5170swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5170
#print axioms sourceMap5170swap_checked
#print axioms fusedMap5170swap_checked
#print axioms certified5170swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
