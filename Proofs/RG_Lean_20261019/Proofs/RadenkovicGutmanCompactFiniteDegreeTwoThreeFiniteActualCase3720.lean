/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3720 : Family 6 := level6.get ⟨31,by decide⟩
def sourceMap3720 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (sourceLabel 6 0 8 v)
def fusedMap3720 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 0 8 v)
theorem sourceMap3720_checked : acceptsGraphIso
    (source (graph core3720) (root 6) 0 8) DegreeTwoThreeSpectrum5552.graph sourceMap3720=true := by decide +kernel
theorem fusedMap3720_checked : acceptsGraphIso
    (fused (graph core3720) (root 6) 0 8) DegreeTwoThreeSpectrum5021.graph fusedMap3720=true := by decide +kernel
theorem certified3720 : Certified (graph core3720) (root 6) 0 8 :=
  of_native_maps core3720 DegreeTwoThreeSpectrum5552.graph DegreeTwoThreeSpectrum5021.graph
    sourceMap3720 fusedMap3720 sourceMap3720_checked fusedMap3720_checked
    DegreeTwoThreeFiniteComparisons.comparison3720
#print axioms sourceMap3720_checked
#print axioms fusedMap3720_checked
#print axioms certified3720
def sourceMap3720swap : (Vertices 6 ⊕ Fin 9 ⊕ Fin 1) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,11,12,13,14,15,16,10] (sourceLabel 6 8 0 v)
def fusedMap3720swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 8 0 v)
theorem sourceMap3720swap_checked : acceptsGraphIso
    (source (graph core3720) (root 6) 8 0) DegreeTwoThreeSpectrum5552.graph sourceMap3720swap=true := by decide +kernel
theorem fusedMap3720swap_checked : acceptsGraphIso
    (fused (graph core3720) (root 6) 8 0) DegreeTwoThreeSpectrum5021.graph fusedMap3720swap=true := by decide +kernel
theorem certified3720swap : Certified (graph core3720) (root 6) 8 0 :=
  of_native_maps core3720 DegreeTwoThreeSpectrum5552.graph DegreeTwoThreeSpectrum5021.graph
    sourceMap3720swap fusedMap3720swap sourceMap3720swap_checked fusedMap3720swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3720
#print axioms sourceMap3720swap_checked
#print axioms fusedMap3720swap_checked
#print axioms certified3720swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
