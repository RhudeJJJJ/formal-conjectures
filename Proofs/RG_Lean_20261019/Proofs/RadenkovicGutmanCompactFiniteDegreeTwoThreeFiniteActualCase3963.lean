/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3963 : Family 7 := level7.get ⟨48,by decide⟩
def sourceMap3963 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3963 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3963_checked : acceptsGraphIso
    (source (graph core3963) (root 7) 1 5) DegreeTwoThreeSpectrum4528.graph sourceMap3963=true := by decide +kernel
theorem fusedMap3963_checked : acceptsGraphIso
    (fused (graph core3963) (root 7) 1 5) DegreeTwoThreeSpectrum4040.graph fusedMap3963=true := by decide +kernel
theorem certified3963 : Certified (graph core3963) (root 7) 1 5 :=
  of_native_maps core3963 DegreeTwoThreeSpectrum4528.graph DegreeTwoThreeSpectrum4040.graph
    sourceMap3963 fusedMap3963 sourceMap3963_checked fusedMap3963_checked
    DegreeTwoThreeFiniteComparisons.comparison3963
#print axioms sourceMap3963_checked
#print axioms fusedMap3963_checked
#print axioms certified3963
def sourceMap3963swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,15,9,10] (sourceLabel 7 5 1 v)
def fusedMap3963swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3963swap_checked : acceptsGraphIso
    (source (graph core3963) (root 7) 5 1) DegreeTwoThreeSpectrum4528.graph sourceMap3963swap=true := by decide +kernel
theorem fusedMap3963swap_checked : acceptsGraphIso
    (fused (graph core3963) (root 7) 5 1) DegreeTwoThreeSpectrum4040.graph fusedMap3963swap=true := by decide +kernel
theorem certified3963swap : Certified (graph core3963) (root 7) 5 1 :=
  of_native_maps core3963 DegreeTwoThreeSpectrum4528.graph DegreeTwoThreeSpectrum4040.graph
    sourceMap3963swap fusedMap3963swap sourceMap3963swap_checked fusedMap3963swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3963
#print axioms sourceMap3963swap_checked
#print axioms fusedMap3963swap_checked
#print axioms certified3963swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
