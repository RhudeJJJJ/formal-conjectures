/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3648 : Family 6 := level6.get ⟨13,by decide⟩
def sourceMap3648 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (sourceLabel 6 0 7 v)
def fusedMap3648 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 0 7 v)
theorem sourceMap3648_checked : acceptsGraphIso
    (source (graph core3648) (root 6) 0 7) DegreeTwoThreeSpectrum4042.graph sourceMap3648=true := by decide +kernel
theorem fusedMap3648_checked : acceptsGraphIso
    (fused (graph core3648) (root 6) 0 7) DegreeTwoThreeSpectrum3865.graph fusedMap3648=true := by decide +kernel
theorem certified3648 : Certified (graph core3648) (root 6) 0 7 :=
  of_native_maps core3648 DegreeTwoThreeSpectrum4042.graph DegreeTwoThreeSpectrum3865.graph
    sourceMap3648 fusedMap3648 sourceMap3648_checked fusedMap3648_checked
    DegreeTwoThreeFiniteComparisons.comparison3648
#print axioms sourceMap3648_checked
#print axioms fusedMap3648_checked
#print axioms certified3648
def sourceMap3648swap : (Vertices 6 ⊕ Fin 8 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,15,9] (sourceLabel 6 7 0 v)
def fusedMap3648swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 7 0 v)
theorem sourceMap3648swap_checked : acceptsGraphIso
    (source (graph core3648) (root 6) 7 0) DegreeTwoThreeSpectrum4042.graph sourceMap3648swap=true := by decide +kernel
theorem fusedMap3648swap_checked : acceptsGraphIso
    (fused (graph core3648) (root 6) 7 0) DegreeTwoThreeSpectrum3865.graph fusedMap3648swap=true := by decide +kernel
theorem certified3648swap : Certified (graph core3648) (root 6) 7 0 :=
  of_native_maps core3648 DegreeTwoThreeSpectrum4042.graph DegreeTwoThreeSpectrum3865.graph
    sourceMap3648swap fusedMap3648swap sourceMap3648swap_checked fusedMap3648swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3648
#print axioms sourceMap3648swap_checked
#print axioms fusedMap3648swap_checked
#print axioms certified3648swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
