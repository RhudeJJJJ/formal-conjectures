/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3991 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap3991 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (sourceLabel 4 1 6 v)
def fusedMap3991 : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 1 6 v)
theorem sourceMap3991_checked : acceptsGraphIso
    (source (graph core3991) (root 4) 1 6) DegreeTwoThreeSpectrum1804.graph sourceMap3991=true := by decide +kernel
theorem fusedMap3991_checked : acceptsGraphIso
    (fused (graph core3991) (root 4) 1 6) DegreeTwoThreeSpectrum1716.graph fusedMap3991=true := by decide +kernel
theorem certified3991 : Certified (graph core3991) (root 4) 1 6 :=
  of_native_maps core3991 DegreeTwoThreeSpectrum1804.graph DegreeTwoThreeSpectrum1716.graph
    sourceMap3991 fusedMap3991 sourceMap3991_checked fusedMap3991_checked
    DegreeTwoThreeFiniteComparisons.comparison3991
#print axioms sourceMap3991_checked
#print axioms fusedMap3991_checked
#print axioms certified3991
def sourceMap3991swap : (Vertices 4 ⊕ Fin 7 ⊕ Fin 2) → Fin 14 :=
  fun v => ![2,3,4,5,6,1,0,9,10,11,12,13,7,8] (sourceLabel 4 6 1 v)
def fusedMap3991swap : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 6 1 v)
theorem sourceMap3991swap_checked : acceptsGraphIso
    (source (graph core3991) (root 4) 6 1) DegreeTwoThreeSpectrum1804.graph sourceMap3991swap=true := by decide +kernel
theorem fusedMap3991swap_checked : acceptsGraphIso
    (fused (graph core3991) (root 4) 6 1) DegreeTwoThreeSpectrum1716.graph fusedMap3991swap=true := by decide +kernel
theorem certified3991swap : Certified (graph core3991) (root 4) 6 1 :=
  of_native_maps core3991 DegreeTwoThreeSpectrum1804.graph DegreeTwoThreeSpectrum1716.graph
    sourceMap3991swap fusedMap3991swap sourceMap3991swap_checked fusedMap3991swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3991
#print axioms sourceMap3991swap_checked
#print axioms fusedMap3991swap_checked
#print axioms certified3991swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
