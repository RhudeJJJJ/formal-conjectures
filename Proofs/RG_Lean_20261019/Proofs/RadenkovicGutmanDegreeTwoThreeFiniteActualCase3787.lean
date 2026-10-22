/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3787 : Family 6 := level6.get ⟨38,by decide⟩
def sourceMap3787 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,9,7,8,0,10,11,12,13] (sourceLabel 6 1 4 v)
def fusedMap3787 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 1 4 v)
theorem sourceMap3787_checked : acceptsGraphIso
    (source (graph core3787) (root 6) 1 4) DegreeTwoThreeSpectrum1932.graph sourceMap3787=true := by decide +kernel
theorem fusedMap3787_checked : acceptsGraphIso
    (fused (graph core3787) (root 6) 1 4) DegreeTwoThreeSpectrum1739.graph fusedMap3787=true := by decide +kernel
theorem certified3787 : Certified (graph core3787) (root 6) 1 4 :=
  of_native_maps core3787 DegreeTwoThreeSpectrum1932.graph DegreeTwoThreeSpectrum1739.graph
    sourceMap3787 fusedMap3787 sourceMap3787_checked fusedMap3787_checked
    DegreeTwoThreeFiniteComparisons.comparison3787
#print axioms sourceMap3787_checked
#print axioms fusedMap3787_checked
#print axioms certified3787
def sourceMap3787swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 2) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,9,0,10,11,12,13,7,8] (sourceLabel 6 4 1 v)
def fusedMap3787swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 4 1 v)
theorem sourceMap3787swap_checked : acceptsGraphIso
    (source (graph core3787) (root 6) 4 1) DegreeTwoThreeSpectrum1932.graph sourceMap3787swap=true := by decide +kernel
theorem fusedMap3787swap_checked : acceptsGraphIso
    (fused (graph core3787) (root 6) 4 1) DegreeTwoThreeSpectrum1739.graph fusedMap3787swap=true := by decide +kernel
theorem certified3787swap : Certified (graph core3787) (root 6) 4 1 :=
  of_native_maps core3787 DegreeTwoThreeSpectrum1932.graph DegreeTwoThreeSpectrum1739.graph
    sourceMap3787swap fusedMap3787swap sourceMap3787swap_checked fusedMap3787swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3787
#print axioms sourceMap3787swap_checked
#print axioms fusedMap3787swap_checked
#print axioms certified3787swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
