/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3944 : Family 6 := level6.get ⟨31,by decide⟩
def sourceMap3944 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 6 1 5 v)
def fusedMap3944 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 1 5 v)
theorem sourceMap3944_checked : acceptsGraphIso
    (source (graph core3944) (root 6) 1 5) DegreeTwoThreeSpectrum2739.graph sourceMap3944=true := by decide +kernel
theorem fusedMap3944_checked : acceptsGraphIso
    (fused (graph core3944) (root 6) 1 5) DegreeTwoThreeSpectrum2360.graph fusedMap3944=true := by decide +kernel
theorem certified3944 : Certified (graph core3944) (root 6) 1 5 :=
  of_native_maps core3944 DegreeTwoThreeSpectrum2739.graph DegreeTwoThreeSpectrum2360.graph
    sourceMap3944 fusedMap3944 sourceMap3944_checked fusedMap3944_checked
    DegreeTwoThreeFiniteComparisons.comparison3944
#print axioms sourceMap3944_checked
#print axioms fusedMap3944_checked
#print axioms certified3944
def sourceMap3944swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,10,11,12,13,14,8,9] (sourceLabel 6 5 1 v)
def fusedMap3944swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 5 1 v)
theorem sourceMap3944swap_checked : acceptsGraphIso
    (source (graph core3944) (root 6) 5 1) DegreeTwoThreeSpectrum2739.graph sourceMap3944swap=true := by decide +kernel
theorem fusedMap3944swap_checked : acceptsGraphIso
    (fused (graph core3944) (root 6) 5 1) DegreeTwoThreeSpectrum2360.graph fusedMap3944swap=true := by decide +kernel
theorem certified3944swap : Certified (graph core3944) (root 6) 5 1 :=
  of_native_maps core3944 DegreeTwoThreeSpectrum2739.graph DegreeTwoThreeSpectrum2360.graph
    sourceMap3944swap fusedMap3944swap sourceMap3944swap_checked fusedMap3944swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3944
#print axioms sourceMap3944swap_checked
#print axioms fusedMap3944swap_checked
#print axioms certified3944swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
