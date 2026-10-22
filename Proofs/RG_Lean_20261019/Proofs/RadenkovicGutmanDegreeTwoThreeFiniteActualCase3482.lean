/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3482 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap3482 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (sourceLabel 5 0 6 v)
def fusedMap3482 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 0 6 v)
theorem sourceMap3482_checked : acceptsGraphIso
    (source (graph core3482) (root 5) 0 6) DegreeTwoThreeSpectrum1836.graph sourceMap3482=true := by decide +kernel
theorem fusedMap3482_checked : acceptsGraphIso
    (fused (graph core3482) (root 5) 0 6) DegreeTwoThreeSpectrum1718.graph fusedMap3482=true := by decide +kernel
theorem certified3482 : Certified (graph core3482) (root 5) 0 6 :=
  of_native_maps core3482 DegreeTwoThreeSpectrum1836.graph DegreeTwoThreeSpectrum1718.graph
    sourceMap3482 fusedMap3482 sourceMap3482_checked fusedMap3482_checked
    DegreeTwoThreeFiniteComparisons.comparison3482
#print axioms sourceMap3482_checked
#print axioms fusedMap3482_checked
#print axioms certified3482
def sourceMap3482swap : (Vertices 5 ⊕ Fin 7 ⊕ Fin 1) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,9,10,11,12,13,8] (sourceLabel 5 6 0 v)
def fusedMap3482swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 6 0 v)
theorem sourceMap3482swap_checked : acceptsGraphIso
    (source (graph core3482) (root 5) 6 0) DegreeTwoThreeSpectrum1836.graph sourceMap3482swap=true := by decide +kernel
theorem fusedMap3482swap_checked : acceptsGraphIso
    (fused (graph core3482) (root 5) 6 0) DegreeTwoThreeSpectrum1718.graph fusedMap3482swap=true := by decide +kernel
theorem certified3482swap : Certified (graph core3482) (root 5) 6 0 :=
  of_native_maps core3482 DegreeTwoThreeSpectrum1836.graph DegreeTwoThreeSpectrum1718.graph
    sourceMap3482swap fusedMap3482swap sourceMap3482swap_checked fusedMap3482swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3482
#print axioms sourceMap3482swap_checked
#print axioms fusedMap3482swap_checked
#print axioms certified3482swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
