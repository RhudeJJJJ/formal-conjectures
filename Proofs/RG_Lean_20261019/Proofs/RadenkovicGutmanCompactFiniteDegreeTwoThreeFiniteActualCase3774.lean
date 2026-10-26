/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3774 : Family 6 := level6.get ⟨5,by decide⟩
def sourceMap3774 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,13,11,12,6,7,8,9,10] (sourceLabel 6 1 4 v)
def fusedMap3774 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13] (fusedLabel 6 1 4 v)
theorem sourceMap3774_checked : acceptsGraphIso
    (source (graph core3774) (root 6) 1 4) DegreeTwoThreeSpectrum1924.graph sourceMap3774=true := by decide +kernel
theorem fusedMap3774_checked : acceptsGraphIso
    (fused (graph core3774) (root 6) 1 4) DegreeTwoThreeSpectrum1737.graph fusedMap3774=true := by decide +kernel
theorem certified3774 : Certified (graph core3774) (root 6) 1 4 :=
  of_native_maps core3774 DegreeTwoThreeSpectrum1924.graph DegreeTwoThreeSpectrum1737.graph
    sourceMap3774 fusedMap3774 sourceMap3774_checked fusedMap3774_checked
    DegreeTwoThreeFiniteComparisons.comparison3774
#print axioms sourceMap3774_checked
#print axioms fusedMap3774_checked
#print axioms certified3774
def sourceMap3774swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 2) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,13,6,7,8,9,10,11,12] (sourceLabel 6 4 1 v)
def fusedMap3774swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13] (fusedLabel 6 4 1 v)
theorem sourceMap3774swap_checked : acceptsGraphIso
    (source (graph core3774) (root 6) 4 1) DegreeTwoThreeSpectrum1924.graph sourceMap3774swap=true := by decide +kernel
theorem fusedMap3774swap_checked : acceptsGraphIso
    (fused (graph core3774) (root 6) 4 1) DegreeTwoThreeSpectrum1737.graph fusedMap3774swap=true := by decide +kernel
theorem certified3774swap : Certified (graph core3774) (root 6) 4 1 :=
  of_native_maps core3774 DegreeTwoThreeSpectrum1924.graph DegreeTwoThreeSpectrum1737.graph
    sourceMap3774swap fusedMap3774swap sourceMap3774swap_checked fusedMap3774swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3774
#print axioms sourceMap3774swap_checked
#print axioms fusedMap3774swap_checked
#print axioms certified3774swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
