/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3328 : Family 9 := level9.get ⟨309,by decide⟩
def sourceMap3328 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3328 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3328_checked : acceptsGraphIso
    (source (graph core3328) (root 9) 0 5) DegreeTwoThreeSpectrum5917.graph sourceMap3328=true := by decide +kernel
theorem fusedMap3328_checked : acceptsGraphIso
    (fused (graph core3328) (root 9) 0 5) DegreeTwoThreeSpectrum5918.graph fusedMap3328=true := by decide +kernel
theorem certified3328 : Certified (graph core3328) (root 9) 0 5 :=
  of_native_maps core3328 DegreeTwoThreeSpectrum5917.graph DegreeTwoThreeSpectrum5918.graph
    sourceMap3328 fusedMap3328 sourceMap3328_checked fusedMap3328_checked
    DegreeTwoThreeFiniteComparisons.comparison3328
#print axioms sourceMap3328_checked
#print axioms fusedMap3328_checked
#print axioms certified3328
def sourceMap3328swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3328swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3328swap_checked : acceptsGraphIso
    (source (graph core3328) (root 9) 5 0) DegreeTwoThreeSpectrum5917.graph sourceMap3328swap=true := by decide +kernel
theorem fusedMap3328swap_checked : acceptsGraphIso
    (fused (graph core3328) (root 9) 5 0) DegreeTwoThreeSpectrum5918.graph fusedMap3328swap=true := by decide +kernel
theorem certified3328swap : Certified (graph core3328) (root 9) 5 0 :=
  of_native_maps core3328 DegreeTwoThreeSpectrum5917.graph DegreeTwoThreeSpectrum5918.graph
    sourceMap3328swap fusedMap3328swap sourceMap3328swap_checked fusedMap3328swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3328
#print axioms sourceMap3328swap_checked
#print axioms fusedMap3328swap_checked
#print axioms certified3328swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
