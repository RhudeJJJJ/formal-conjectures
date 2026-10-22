/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1296 : Family 9 := level9.get ⟨347,by decide⟩
def sourceMap1296 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1296 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1296_checked : acceptsGraphIso
    (source (graph core1296) (root 9) 0 2) DegreeTwoThreeSpectrum1976.graph sourceMap1296=true := by decide +kernel
theorem fusedMap1296_checked : acceptsGraphIso
    (fused (graph core1296) (root 9) 0 2) DegreeTwoThreeSpectrum1977.graph fusedMap1296=true := by decide +kernel
theorem certified1296 : Certified (graph core1296) (root 9) 0 2 :=
  of_native_maps core1296 DegreeTwoThreeSpectrum1976.graph DegreeTwoThreeSpectrum1977.graph
    sourceMap1296 fusedMap1296 sourceMap1296_checked fusedMap1296_checked
    DegreeTwoThreeFiniteComparisons.comparison1296
#print axioms sourceMap1296_checked
#print axioms fusedMap1296_checked
#print axioms certified1296
def sourceMap1296swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1296swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1296swap_checked : acceptsGraphIso
    (source (graph core1296) (root 9) 2 0) DegreeTwoThreeSpectrum1976.graph sourceMap1296swap=true := by decide +kernel
theorem fusedMap1296swap_checked : acceptsGraphIso
    (fused (graph core1296) (root 9) 2 0) DegreeTwoThreeSpectrum1977.graph fusedMap1296swap=true := by decide +kernel
theorem certified1296swap : Certified (graph core1296) (root 9) 2 0 :=
  of_native_maps core1296 DegreeTwoThreeSpectrum1976.graph DegreeTwoThreeSpectrum1977.graph
    sourceMap1296swap fusedMap1296swap sourceMap1296swap_checked fusedMap1296swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1296
#print axioms sourceMap1296swap_checked
#print axioms fusedMap1296swap_checked
#print axioms certified1296swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
