/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3101 : Family 6 := level6.get ⟨39,by decide⟩
def sourceMap3101 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 6) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13] (sourceLabel 6 0 5 v)
def fusedMap3101 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 0 5 v)
theorem sourceMap3101_checked : acceptsGraphIso
    (source (graph core3101) (root 6) 0 5) DegreeTwoThreeSpectrum1953.graph sourceMap3101=true := by decide +kernel
theorem fusedMap3101_checked : acceptsGraphIso
    (fused (graph core3101) (root 6) 0 5) DegreeTwoThreeSpectrum1742.graph fusedMap3101=true := by decide +kernel
theorem certified3101 : Certified (graph core3101) (root 6) 0 5 :=
  of_native_maps core3101 DegreeTwoThreeSpectrum1953.graph DegreeTwoThreeSpectrum1742.graph
    sourceMap3101 fusedMap3101 sourceMap3101_checked fusedMap3101_checked
    DegreeTwoThreeFiniteComparisons.comparison3101
#print axioms sourceMap3101_checked
#print axioms fusedMap3101_checked
#print axioms certified3101
def sourceMap3101swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 1) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,9] (sourceLabel 6 5 0 v)
def fusedMap3101swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 5 0 v)
theorem sourceMap3101swap_checked : acceptsGraphIso
    (source (graph core3101) (root 6) 5 0) DegreeTwoThreeSpectrum1953.graph sourceMap3101swap=true := by decide +kernel
theorem fusedMap3101swap_checked : acceptsGraphIso
    (fused (graph core3101) (root 6) 5 0) DegreeTwoThreeSpectrum1742.graph fusedMap3101swap=true := by decide +kernel
theorem certified3101swap : Certified (graph core3101) (root 6) 5 0 :=
  of_native_maps core3101 DegreeTwoThreeSpectrum1953.graph DegreeTwoThreeSpectrum1742.graph
    sourceMap3101swap fusedMap3101swap sourceMap3101swap_checked fusedMap3101swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3101
#print axioms sourceMap3101swap_checked
#print axioms fusedMap3101swap_checked
#print axioms certified3101swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
