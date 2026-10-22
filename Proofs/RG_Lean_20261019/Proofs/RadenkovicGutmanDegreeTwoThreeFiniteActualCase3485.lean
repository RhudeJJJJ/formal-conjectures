/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3485 : Family 5 := level5.get ⟨15,by decide⟩
def sourceMap3485 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (sourceLabel 5 0 6 v)
def fusedMap3485 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13] (fusedLabel 5 0 6 v)
theorem sourceMap3485_checked : acceptsGraphIso
    (source (graph core3485) (root 5) 0 6) DegreeTwoThreeSpectrum1758.graph sourceMap3485=true := by decide +kernel
theorem fusedMap3485_checked : acceptsGraphIso
    (fused (graph core3485) (root 5) 0 6) DegreeTwoThreeSpectrum1761.graph fusedMap3485=true := by decide +kernel
theorem certified3485 : Certified (graph core3485) (root 5) 0 6 :=
  of_native_maps core3485 DegreeTwoThreeSpectrum1758.graph DegreeTwoThreeSpectrum1761.graph
    sourceMap3485 fusedMap3485 sourceMap3485_checked fusedMap3485_checked
    DegreeTwoThreeFiniteComparisons.comparison3485
#print axioms sourceMap3485_checked
#print axioms fusedMap3485_checked
#print axioms certified3485
def sourceMap3485swap : (Vertices 5 ⊕ Fin 7 ⊕ Fin 1) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,9,10,11,12,13,8] (sourceLabel 5 6 0 v)
def fusedMap3485swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13] (fusedLabel 5 6 0 v)
theorem sourceMap3485swap_checked : acceptsGraphIso
    (source (graph core3485) (root 5) 6 0) DegreeTwoThreeSpectrum1758.graph sourceMap3485swap=true := by decide +kernel
theorem fusedMap3485swap_checked : acceptsGraphIso
    (fused (graph core3485) (root 5) 6 0) DegreeTwoThreeSpectrum1761.graph fusedMap3485swap=true := by decide +kernel
theorem certified3485swap : Certified (graph core3485) (root 5) 6 0 :=
  of_native_maps core3485 DegreeTwoThreeSpectrum1758.graph DegreeTwoThreeSpectrum1761.graph
    sourceMap3485swap fusedMap3485swap sourceMap3485swap_checked fusedMap3485swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3485
#print axioms sourceMap3485swap_checked
#print axioms fusedMap3485swap_checked
#print axioms certified3485swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
