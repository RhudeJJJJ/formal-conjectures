/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3876 : Family 8 := level8.get ⟨158,by decide⟩
def sourceMap3876 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3876 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3876_checked : acceptsGraphIso
    (source (graph core3876) (root 8) 1 4) DegreeTwoThreeSpectrum4526.graph sourceMap3876=true := by decide +kernel
theorem fusedMap3876_checked : acceptsGraphIso
    (fused (graph core3876) (root 8) 1 4) DegreeTwoThreeSpectrum4037.graph fusedMap3876=true := by decide +kernel
theorem certified3876 : Certified (graph core3876) (root 8) 1 4 :=
  of_native_maps core3876 DegreeTwoThreeSpectrum4526.graph DegreeTwoThreeSpectrum4037.graph
    sourceMap3876 fusedMap3876 sourceMap3876_checked fusedMap3876_checked
    DegreeTwoThreeFiniteComparisons.comparison3876
#print axioms sourceMap3876_checked
#print axioms fusedMap3876_checked
#print axioms certified3876
def sourceMap3876swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3876swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3876swap_checked : acceptsGraphIso
    (source (graph core3876) (root 8) 4 1) DegreeTwoThreeSpectrum4526.graph sourceMap3876swap=true := by decide +kernel
theorem fusedMap3876swap_checked : acceptsGraphIso
    (fused (graph core3876) (root 8) 4 1) DegreeTwoThreeSpectrum4037.graph fusedMap3876swap=true := by decide +kernel
theorem certified3876swap : Certified (graph core3876) (root 8) 4 1 :=
  of_native_maps core3876 DegreeTwoThreeSpectrum4526.graph DegreeTwoThreeSpectrum4037.graph
    sourceMap3876swap fusedMap3876swap sourceMap3876swap_checked fusedMap3876swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3876
#print axioms sourceMap3876swap_checked
#print axioms fusedMap3876swap_checked
#print axioms certified3876swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
