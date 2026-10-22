/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3937 : Family 6 := level6.get ⟨16,by decide⟩
def sourceMap3937 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,9,7,8,0,10,11,12,13,14] (sourceLabel 6 1 5 v)
def fusedMap3937 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 1 5 v)
theorem sourceMap3937_checked : acceptsGraphIso
    (source (graph core3937) (root 6) 1 5) DegreeTwoThreeSpectrum2919.graph sourceMap3937=true := by decide +kernel
theorem fusedMap3937_checked : acceptsGraphIso
    (fused (graph core3937) (root 6) 1 5) DegreeTwoThreeSpectrum2398.graph fusedMap3937=true := by decide +kernel
theorem certified3937 : Certified (graph core3937) (root 6) 1 5 :=
  of_native_maps core3937 DegreeTwoThreeSpectrum2919.graph DegreeTwoThreeSpectrum2398.graph
    sourceMap3937 fusedMap3937 sourceMap3937_checked fusedMap3937_checked
    DegreeTwoThreeFiniteComparisons.comparison3937
#print axioms sourceMap3937_checked
#print axioms fusedMap3937_checked
#print axioms certified3937
def sourceMap3937swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,9,0,10,11,12,13,14,7,8] (sourceLabel 6 5 1 v)
def fusedMap3937swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 5 1 v)
theorem sourceMap3937swap_checked : acceptsGraphIso
    (source (graph core3937) (root 6) 5 1) DegreeTwoThreeSpectrum2919.graph sourceMap3937swap=true := by decide +kernel
theorem fusedMap3937swap_checked : acceptsGraphIso
    (fused (graph core3937) (root 6) 5 1) DegreeTwoThreeSpectrum2398.graph fusedMap3937swap=true := by decide +kernel
theorem certified3937swap : Certified (graph core3937) (root 6) 5 1 :=
  of_native_maps core3937 DegreeTwoThreeSpectrum2919.graph DegreeTwoThreeSpectrum2398.graph
    sourceMap3937swap fusedMap3937swap sourceMap3937swap_checked fusedMap3937swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3937
#print axioms sourceMap3937swap_checked
#print axioms fusedMap3937swap_checked
#print axioms certified3937swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
