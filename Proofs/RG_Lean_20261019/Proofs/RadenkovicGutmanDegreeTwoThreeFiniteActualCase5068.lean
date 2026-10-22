/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5068 : Family 6 := level6.get ⟨13,by decide⟩
def sourceMap5068 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,9,6,7,8,10,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap5068 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap5068_checked : acceptsGraphIso
    (source (graph core5068) (root 6) 2 4) DegreeTwoThreeSpectrum2772.graph sourceMap5068=true := by decide +kernel
theorem fusedMap5068_checked : acceptsGraphIso
    (fused (graph core5068) (root 6) 2 4) DegreeTwoThreeSpectrum2370.graph fusedMap5068=true := by decide +kernel
theorem certified5068 : Certified (graph core5068) (root 6) 2 4 :=
  of_native_maps core5068 DegreeTwoThreeSpectrum2772.graph DegreeTwoThreeSpectrum2370.graph
    sourceMap5068 fusedMap5068 sourceMap5068_checked fusedMap5068_checked
    DegreeTwoThreeFiniteComparisons.comparison5068
#print axioms sourceMap5068_checked
#print axioms fusedMap5068_checked
#print axioms certified5068
def sourceMap5068swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,14,6,7,8] (sourceLabel 6 4 2 v)
def fusedMap5068swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap5068swap_checked : acceptsGraphIso
    (source (graph core5068) (root 6) 4 2) DegreeTwoThreeSpectrum2772.graph sourceMap5068swap=true := by decide +kernel
theorem fusedMap5068swap_checked : acceptsGraphIso
    (fused (graph core5068) (root 6) 4 2) DegreeTwoThreeSpectrum2370.graph fusedMap5068swap=true := by decide +kernel
theorem certified5068swap : Certified (graph core5068) (root 6) 4 2 :=
  of_native_maps core5068 DegreeTwoThreeSpectrum2772.graph DegreeTwoThreeSpectrum2370.graph
    sourceMap5068swap fusedMap5068swap sourceMap5068swap_checked fusedMap5068swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5068
#print axioms sourceMap5068swap_checked
#print axioms fusedMap5068swap_checked
#print axioms certified5068swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
