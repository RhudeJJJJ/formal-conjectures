/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3992 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap3992 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,8,6,7,0,9,10,11,12,13,14] (sourceLabel 5 1 6 v)
def fusedMap3992 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13,14] (fusedLabel 5 1 6 v)
theorem sourceMap3992_checked : acceptsGraphIso
    (source (graph core3992) (root 5) 1 6) DegreeTwoThreeSpectrum2410.graph sourceMap3992=true := by decide +kernel
theorem fusedMap3992_checked : acceptsGraphIso
    (fused (graph core3992) (root 5) 1 6) DegreeTwoThreeSpectrum2312.graph fusedMap3992=true := by decide +kernel
theorem certified3992 : Certified (graph core3992) (root 5) 1 6 :=
  of_native_maps core3992 DegreeTwoThreeSpectrum2410.graph DegreeTwoThreeSpectrum2312.graph
    sourceMap3992 fusedMap3992 sourceMap3992_checked fusedMap3992_checked
    DegreeTwoThreeFiniteComparisons.comparison3992
#print axioms sourceMap3992_checked
#print axioms fusedMap3992_checked
#print axioms certified3992
def sourceMap3992swap : (Vertices 5 ⊕ Fin 7 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,8,0,9,10,11,12,13,14,6,7] (sourceLabel 5 6 1 v)
def fusedMap3992swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13,14] (fusedLabel 5 6 1 v)
theorem sourceMap3992swap_checked : acceptsGraphIso
    (source (graph core3992) (root 5) 6 1) DegreeTwoThreeSpectrum2410.graph sourceMap3992swap=true := by decide +kernel
theorem fusedMap3992swap_checked : acceptsGraphIso
    (fused (graph core3992) (root 5) 6 1) DegreeTwoThreeSpectrum2312.graph fusedMap3992swap=true := by decide +kernel
theorem certified3992swap : Certified (graph core3992) (root 5) 6 1 :=
  of_native_maps core3992 DegreeTwoThreeSpectrum2410.graph DegreeTwoThreeSpectrum2312.graph
    sourceMap3992swap fusedMap3992swap sourceMap3992swap_checked fusedMap3992swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3992
#print axioms sourceMap3992swap_checked
#print axioms fusedMap3992swap_checked
#print axioms certified3992swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
