/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3665 : Family 7 := level7.get ⟨20,by decide⟩
def sourceMap3665 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3665 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3665_checked : acceptsGraphIso
    (source (graph core3665) (root 7) 0 7) DegreeTwoThreeSpectrum5068.graph sourceMap3665=true := by decide +kernel
theorem fusedMap3665_checked : acceptsGraphIso
    (fused (graph core3665) (root 7) 0 7) DegreeTwoThreeSpectrum5071.graph fusedMap3665=true := by decide +kernel
theorem certified3665 : Certified (graph core3665) (root 7) 0 7 :=
  of_native_maps core3665 DegreeTwoThreeSpectrum5068.graph DegreeTwoThreeSpectrum5071.graph
    sourceMap3665 fusedMap3665 sourceMap3665_checked fusedMap3665_checked
    DegreeTwoThreeFiniteComparisons.comparison3665
#print axioms sourceMap3665_checked
#print axioms fusedMap3665_checked
#print axioms certified3665
def sourceMap3665swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,15,16,9] (sourceLabel 7 7 0 v)
def fusedMap3665swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3665swap_checked : acceptsGraphIso
    (source (graph core3665) (root 7) 7 0) DegreeTwoThreeSpectrum5068.graph sourceMap3665swap=true := by decide +kernel
theorem fusedMap3665swap_checked : acceptsGraphIso
    (fused (graph core3665) (root 7) 7 0) DegreeTwoThreeSpectrum5071.graph fusedMap3665swap=true := by decide +kernel
theorem certified3665swap : Certified (graph core3665) (root 7) 7 0 :=
  of_native_maps core3665 DegreeTwoThreeSpectrum5068.graph DegreeTwoThreeSpectrum5071.graph
    sourceMap3665swap fusedMap3665swap sourceMap3665swap_checked fusedMap3665swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3665
#print axioms sourceMap3665swap_checked
#print axioms fusedMap3665swap_checked
#print axioms certified3665swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
