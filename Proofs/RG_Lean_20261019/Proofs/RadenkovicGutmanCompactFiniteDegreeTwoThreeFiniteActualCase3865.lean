/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3865 : Family 8 := level8.get ⟨129,by decide⟩
def sourceMap3865 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3865 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3865_checked : acceptsGraphIso
    (source (graph core3865) (root 8) 1 4) DegreeTwoThreeSpectrum4378.graph sourceMap3865=true := by decide +kernel
theorem fusedMap3865_checked : acceptsGraphIso
    (fused (graph core3865) (root 8) 1 4) DegreeTwoThreeSpectrum3960.graph fusedMap3865=true := by decide +kernel
theorem certified3865 : Certified (graph core3865) (root 8) 1 4 :=
  of_native_maps core3865 DegreeTwoThreeSpectrum4378.graph DegreeTwoThreeSpectrum3960.graph
    sourceMap3865 fusedMap3865 sourceMap3865_checked fusedMap3865_checked
    DegreeTwoThreeFiniteComparisons.comparison3865
#print axioms sourceMap3865_checked
#print axioms fusedMap3865_checked
#print axioms certified3865
def sourceMap3865swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3865swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3865swap_checked : acceptsGraphIso
    (source (graph core3865) (root 8) 4 1) DegreeTwoThreeSpectrum4378.graph sourceMap3865swap=true := by decide +kernel
theorem fusedMap3865swap_checked : acceptsGraphIso
    (fused (graph core3865) (root 8) 4 1) DegreeTwoThreeSpectrum3960.graph fusedMap3865swap=true := by decide +kernel
theorem certified3865swap : Certified (graph core3865) (root 8) 4 1 :=
  of_native_maps core3865 DegreeTwoThreeSpectrum4378.graph DegreeTwoThreeSpectrum3960.graph
    sourceMap3865swap fusedMap3865swap sourceMap3865swap_checked fusedMap3865swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3865
#print axioms sourceMap3865swap_checked
#print axioms fusedMap3865swap_checked
#print axioms certified3865swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
