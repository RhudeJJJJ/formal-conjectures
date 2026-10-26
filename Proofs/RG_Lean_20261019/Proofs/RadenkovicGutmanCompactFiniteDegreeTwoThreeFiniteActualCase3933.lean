/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3933 : Family 5 := level5.get ⟨15,by decide⟩
def sourceMap3933 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 6) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13] (sourceLabel 5 1 5 v)
def fusedMap3933 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13] (fusedLabel 5 1 5 v)
theorem sourceMap3933_checked : acceptsGraphIso
    (source (graph core3933) (root 5) 1 5) DegreeTwoThreeSpectrum1994.graph sourceMap3933=true := by decide +kernel
theorem fusedMap3933_checked : acceptsGraphIso
    (fused (graph core3933) (root 5) 1 5) DegreeTwoThreeSpectrum1761.graph fusedMap3933=true := by decide +kernel
theorem certified3933 : Certified (graph core3933) (root 5) 1 5 :=
  of_native_maps core3933 DegreeTwoThreeSpectrum1994.graph DegreeTwoThreeSpectrum1761.graph
    sourceMap3933 fusedMap3933 sourceMap3933_checked fusedMap3933_checked
    DegreeTwoThreeFiniteComparisons.comparison3933
#print axioms sourceMap3933_checked
#print axioms fusedMap3933_checked
#print axioms certified3933
def sourceMap3933swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 2) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,10,11,12,13,8,9] (sourceLabel 5 5 1 v)
def fusedMap3933swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13] (fusedLabel 5 5 1 v)
theorem sourceMap3933swap_checked : acceptsGraphIso
    (source (graph core3933) (root 5) 5 1) DegreeTwoThreeSpectrum1994.graph sourceMap3933swap=true := by decide +kernel
theorem fusedMap3933swap_checked : acceptsGraphIso
    (fused (graph core3933) (root 5) 5 1) DegreeTwoThreeSpectrum1761.graph fusedMap3933swap=true := by decide +kernel
theorem certified3933swap : Certified (graph core3933) (root 5) 5 1 :=
  of_native_maps core3933 DegreeTwoThreeSpectrum1994.graph DegreeTwoThreeSpectrum1761.graph
    sourceMap3933swap fusedMap3933swap sourceMap3933swap_checked fusedMap3933swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3933
#print axioms sourceMap3933swap_checked
#print axioms fusedMap3933swap_checked
#print axioms certified3933swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
