/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3928 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap3928 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,8,6,7,0,9,10,11,12,13] (sourceLabel 5 1 5 v)
def fusedMap3928 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 1 5 v)
theorem sourceMap3928_checked : acceptsGraphIso
    (source (graph core3928) (root 5) 1 5) DegreeTwoThreeSpectrum1914.graph sourceMap3928=true := by decide +kernel
theorem fusedMap3928_checked : acceptsGraphIso
    (fused (graph core3928) (root 5) 1 5) DegreeTwoThreeSpectrum1734.graph fusedMap3928=true := by decide +kernel
theorem certified3928 : Certified (graph core3928) (root 5) 1 5 :=
  of_native_maps core3928 DegreeTwoThreeSpectrum1914.graph DegreeTwoThreeSpectrum1734.graph
    sourceMap3928 fusedMap3928 sourceMap3928_checked fusedMap3928_checked
    DegreeTwoThreeFiniteComparisons.comparison3928
#print axioms sourceMap3928_checked
#print axioms fusedMap3928_checked
#print axioms certified3928
def sourceMap3928swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 2) → Fin 14 :=
  fun v => ![1,2,3,4,5,8,0,9,10,11,12,13,6,7] (sourceLabel 5 5 1 v)
def fusedMap3928swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 5 1 v)
theorem sourceMap3928swap_checked : acceptsGraphIso
    (source (graph core3928) (root 5) 5 1) DegreeTwoThreeSpectrum1914.graph sourceMap3928swap=true := by decide +kernel
theorem fusedMap3928swap_checked : acceptsGraphIso
    (fused (graph core3928) (root 5) 5 1) DegreeTwoThreeSpectrum1734.graph fusedMap3928swap=true := by decide +kernel
theorem certified3928swap : Certified (graph core3928) (root 5) 5 1 :=
  of_native_maps core3928 DegreeTwoThreeSpectrum1914.graph DegreeTwoThreeSpectrum1734.graph
    sourceMap3928swap fusedMap3928swap sourceMap3928swap_checked fusedMap3928swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3928
#print axioms sourceMap3928swap_checked
#print axioms fusedMap3928swap_checked
#print axioms certified3928swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
