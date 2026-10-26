/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3777 : Family 6 := level6.get ⟨16,by decide⟩
def sourceMap3777 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,8,6,7,9,10,11,12,13] (sourceLabel 6 1 4 v)
def fusedMap3777 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13] (fusedLabel 6 1 4 v)
theorem sourceMap3777_checked : acceptsGraphIso
    (source (graph core3777) (root 6) 1 4) DegreeTwoThreeSpectrum1890.graph sourceMap3777=true := by decide +kernel
theorem fusedMap3777_checked : acceptsGraphIso
    (fused (graph core3777) (root 6) 1 4) DegreeTwoThreeSpectrum1725.graph fusedMap3777=true := by decide +kernel
theorem certified3777 : Certified (graph core3777) (root 6) 1 4 :=
  of_native_maps core3777 DegreeTwoThreeSpectrum1890.graph DegreeTwoThreeSpectrum1725.graph
    sourceMap3777 fusedMap3777 sourceMap3777_checked fusedMap3777_checked
    DegreeTwoThreeFiniteComparisons.comparison3777
#print axioms sourceMap3777_checked
#print axioms fusedMap3777_checked
#print axioms certified3777
def sourceMap3777swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 2) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,8,9,10,11,12,13,6,7] (sourceLabel 6 4 1 v)
def fusedMap3777swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13] (fusedLabel 6 4 1 v)
theorem sourceMap3777swap_checked : acceptsGraphIso
    (source (graph core3777) (root 6) 4 1) DegreeTwoThreeSpectrum1890.graph sourceMap3777swap=true := by decide +kernel
theorem fusedMap3777swap_checked : acceptsGraphIso
    (fused (graph core3777) (root 6) 4 1) DegreeTwoThreeSpectrum1725.graph fusedMap3777swap=true := by decide +kernel
theorem certified3777swap : Certified (graph core3777) (root 6) 4 1 :=
  of_native_maps core3777 DegreeTwoThreeSpectrum1890.graph DegreeTwoThreeSpectrum1725.graph
    sourceMap3777swap fusedMap3777swap sourceMap3777swap_checked fusedMap3777swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3777
#print axioms sourceMap3777swap_checked
#print axioms fusedMap3777swap_checked
#print axioms certified3777swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
