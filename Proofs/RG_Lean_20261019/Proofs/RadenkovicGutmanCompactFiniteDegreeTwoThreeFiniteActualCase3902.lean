/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3902 : Family 8 := level8.get ⟨218,by decide⟩
def sourceMap3902 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3902 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3902_checked : acceptsGraphIso
    (source (graph core3902) (root 8) 1 4) DegreeTwoThreeSpectrum4747.graph sourceMap3902=true := by decide +kernel
theorem fusedMap3902_checked : acceptsGraphIso
    (fused (graph core3902) (root 8) 1 4) DegreeTwoThreeSpectrum4306.graph fusedMap3902=true := by decide +kernel
theorem certified3902 : Certified (graph core3902) (root 8) 1 4 :=
  of_native_maps core3902 DegreeTwoThreeSpectrum4747.graph DegreeTwoThreeSpectrum4306.graph
    sourceMap3902 fusedMap3902 sourceMap3902_checked fusedMap3902_checked
    DegreeTwoThreeFiniteComparisons.comparison3902
#print axioms sourceMap3902_checked
#print axioms fusedMap3902_checked
#print axioms certified3902
def sourceMap3902swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,12,13,14,15,10,11] (sourceLabel 8 4 1 v)
def fusedMap3902swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3902swap_checked : acceptsGraphIso
    (source (graph core3902) (root 8) 4 1) DegreeTwoThreeSpectrum4747.graph sourceMap3902swap=true := by decide +kernel
theorem fusedMap3902swap_checked : acceptsGraphIso
    (fused (graph core3902) (root 8) 4 1) DegreeTwoThreeSpectrum4306.graph fusedMap3902swap=true := by decide +kernel
theorem certified3902swap : Certified (graph core3902) (root 8) 4 1 :=
  of_native_maps core3902 DegreeTwoThreeSpectrum4747.graph DegreeTwoThreeSpectrum4306.graph
    sourceMap3902swap fusedMap3902swap sourceMap3902swap_checked fusedMap3902swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3902
#print axioms sourceMap3902swap_checked
#print axioms fusedMap3902swap_checked
#print axioms certified3902swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
