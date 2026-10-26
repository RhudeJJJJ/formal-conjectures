/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3930 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap3930 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,8,6,7,0,9,10,11,12,13] (sourceLabel 5 1 5 v)
def fusedMap3930 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 1 5 v)
theorem sourceMap3930_checked : acceptsGraphIso
    (source (graph core3930) (root 5) 1 5) DegreeTwoThreeSpectrum1832.graph sourceMap3930=true := by decide +kernel
theorem fusedMap3930_checked : acceptsGraphIso
    (fused (graph core3930) (root 5) 1 5) DegreeTwoThreeSpectrum1718.graph fusedMap3930=true := by decide +kernel
theorem certified3930 : Certified (graph core3930) (root 5) 1 5 :=
  of_native_maps core3930 DegreeTwoThreeSpectrum1832.graph DegreeTwoThreeSpectrum1718.graph
    sourceMap3930 fusedMap3930 sourceMap3930_checked fusedMap3930_checked
    DegreeTwoThreeFiniteComparisons.comparison3930
#print axioms sourceMap3930_checked
#print axioms fusedMap3930_checked
#print axioms certified3930
def sourceMap3930swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 2) → Fin 14 :=
  fun v => ![1,2,3,4,5,8,0,9,10,11,12,13,6,7] (sourceLabel 5 5 1 v)
def fusedMap3930swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 5 1 v)
theorem sourceMap3930swap_checked : acceptsGraphIso
    (source (graph core3930) (root 5) 5 1) DegreeTwoThreeSpectrum1832.graph sourceMap3930swap=true := by decide +kernel
theorem fusedMap3930swap_checked : acceptsGraphIso
    (fused (graph core3930) (root 5) 5 1) DegreeTwoThreeSpectrum1718.graph fusedMap3930swap=true := by decide +kernel
theorem certified3930swap : Certified (graph core3930) (root 5) 5 1 :=
  of_native_maps core3930 DegreeTwoThreeSpectrum1832.graph DegreeTwoThreeSpectrum1718.graph
    sourceMap3930swap fusedMap3930swap sourceMap3930swap_checked fusedMap3930swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3930
#print axioms sourceMap3930swap_checked
#print axioms fusedMap3930swap_checked
#print axioms certified3930swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
