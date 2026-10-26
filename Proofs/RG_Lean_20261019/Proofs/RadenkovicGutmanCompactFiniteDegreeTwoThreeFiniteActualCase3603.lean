/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3603 : Family 8 := level8.get ⟨194,by decide⟩
def sourceMap3603 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3603 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3603_checked : acceptsGraphIso
    (source (graph core3603) (root 8) 0 6) DegreeTwoThreeSpectrum6028.graph sourceMap3603=true := by decide +kernel
theorem fusedMap3603_checked : acceptsGraphIso
    (fused (graph core3603) (root 8) 0 6) DegreeTwoThreeSpectrum5145.graph fusedMap3603=true := by decide +kernel
theorem certified3603 : Certified (graph core3603) (root 8) 0 6 :=
  of_native_maps core3603 DegreeTwoThreeSpectrum6028.graph DegreeTwoThreeSpectrum5145.graph
    sourceMap3603 fusedMap3603 sourceMap3603_checked fusedMap3603_checked
    DegreeTwoThreeFiniteComparisons.comparison3603
#print axioms sourceMap3603_checked
#print axioms fusedMap3603_checked
#print axioms certified3603
def sourceMap3603swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3603swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3603swap_checked : acceptsGraphIso
    (source (graph core3603) (root 8) 6 0) DegreeTwoThreeSpectrum6028.graph sourceMap3603swap=true := by decide +kernel
theorem fusedMap3603swap_checked : acceptsGraphIso
    (fused (graph core3603) (root 8) 6 0) DegreeTwoThreeSpectrum5145.graph fusedMap3603swap=true := by decide +kernel
theorem certified3603swap : Certified (graph core3603) (root 8) 6 0 :=
  of_native_maps core3603 DegreeTwoThreeSpectrum6028.graph DegreeTwoThreeSpectrum5145.graph
    sourceMap3603swap fusedMap3603swap sourceMap3603swap_checked fusedMap3603swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3603
#print axioms sourceMap3603swap_checked
#print axioms fusedMap3603swap_checked
#print axioms certified3603swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
