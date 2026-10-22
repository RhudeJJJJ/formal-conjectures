/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3462 : Family 9 := level9.get ⟨644,by decide⟩
def sourceMap3462 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3462 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3462_checked : acceptsGraphIso
    (source (graph core3462) (root 9) 0 5) DegreeTwoThreeSpectrum6535.graph sourceMap3462=true := by decide +kernel
theorem fusedMap3462_checked : acceptsGraphIso
    (fused (graph core3462) (root 9) 0 5) DegreeTwoThreeSpectrum6536.graph fusedMap3462=true := by decide +kernel
theorem certified3462 : Certified (graph core3462) (root 9) 0 5 :=
  of_native_maps core3462 DegreeTwoThreeSpectrum6535.graph DegreeTwoThreeSpectrum6536.graph
    sourceMap3462 fusedMap3462 sourceMap3462_checked fusedMap3462_checked
    DegreeTwoThreeFiniteComparisons.comparison3462
#print axioms sourceMap3462_checked
#print axioms fusedMap3462_checked
#print axioms certified3462
def sourceMap3462swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3462swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3462swap_checked : acceptsGraphIso
    (source (graph core3462) (root 9) 5 0) DegreeTwoThreeSpectrum6535.graph sourceMap3462swap=true := by decide +kernel
theorem fusedMap3462swap_checked : acceptsGraphIso
    (fused (graph core3462) (root 9) 5 0) DegreeTwoThreeSpectrum6536.graph fusedMap3462swap=true := by decide +kernel
theorem certified3462swap : Certified (graph core3462) (root 9) 5 0 :=
  of_native_maps core3462 DegreeTwoThreeSpectrum6535.graph DegreeTwoThreeSpectrum6536.graph
    sourceMap3462swap fusedMap3462swap sourceMap3462swap_checked fusedMap3462swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3462
#print axioms sourceMap3462swap_checked
#print axioms fusedMap3462swap_checked
#print axioms certified3462swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
