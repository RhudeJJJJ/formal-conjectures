/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3929 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap3929 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,8,6,7,0,9,10,11,12,13] (sourceLabel 5 1 5 v)
def fusedMap3929 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 1 5 v)
theorem sourceMap3929_checked : acceptsGraphIso
    (source (graph core3929) (root 5) 1 5) DegreeTwoThreeSpectrum1777.graph sourceMap3929=true := by decide +kernel
theorem fusedMap3929_checked : acceptsGraphIso
    (fused (graph core3929) (root 5) 1 5) DegreeTwoThreeSpectrum1711.graph fusedMap3929=true := by decide +kernel
theorem certified3929 : Certified (graph core3929) (root 5) 1 5 :=
  of_native_maps core3929 DegreeTwoThreeSpectrum1777.graph DegreeTwoThreeSpectrum1711.graph
    sourceMap3929 fusedMap3929 sourceMap3929_checked fusedMap3929_checked
    DegreeTwoThreeFiniteComparisons.comparison3929
#print axioms sourceMap3929_checked
#print axioms fusedMap3929_checked
#print axioms certified3929
def sourceMap3929swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 2) → Fin 14 :=
  fun v => ![1,2,3,4,5,8,0,9,10,11,12,13,6,7] (sourceLabel 5 5 1 v)
def fusedMap3929swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 5 1 v)
theorem sourceMap3929swap_checked : acceptsGraphIso
    (source (graph core3929) (root 5) 5 1) DegreeTwoThreeSpectrum1777.graph sourceMap3929swap=true := by decide +kernel
theorem fusedMap3929swap_checked : acceptsGraphIso
    (fused (graph core3929) (root 5) 5 1) DegreeTwoThreeSpectrum1711.graph fusedMap3929swap=true := by decide +kernel
theorem certified3929swap : Certified (graph core3929) (root 5) 5 1 :=
  of_native_maps core3929 DegreeTwoThreeSpectrum1777.graph DegreeTwoThreeSpectrum1711.graph
    sourceMap3929swap fusedMap3929swap sourceMap3929swap_checked fusedMap3929swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3929
#print axioms sourceMap3929swap_checked
#print axioms fusedMap3929swap_checked
#print axioms certified3929swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
