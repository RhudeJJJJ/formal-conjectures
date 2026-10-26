/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3909 : Family 8 := level8.get ⟨234,by decide⟩
def sourceMap3909 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3909 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3909_checked : acceptsGraphIso
    (source (graph core3909) (root 8) 1 4) DegreeTwoThreeSpectrum4797.graph sourceMap3909=true := by decide +kernel
theorem fusedMap3909_checked : acceptsGraphIso
    (fused (graph core3909) (root 8) 1 4) DegreeTwoThreeSpectrum4406.graph fusedMap3909=true := by decide +kernel
theorem certified3909 : Certified (graph core3909) (root 8) 1 4 :=
  of_native_maps core3909 DegreeTwoThreeSpectrum4797.graph DegreeTwoThreeSpectrum4406.graph
    sourceMap3909 fusedMap3909 sourceMap3909_checked fusedMap3909_checked
    DegreeTwoThreeFiniteComparisons.comparison3909
#print axioms sourceMap3909_checked
#print axioms fusedMap3909_checked
#print axioms certified3909
def sourceMap3909swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,12,13,14,15,10,11] (sourceLabel 8 4 1 v)
def fusedMap3909swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3909swap_checked : acceptsGraphIso
    (source (graph core3909) (root 8) 4 1) DegreeTwoThreeSpectrum4797.graph sourceMap3909swap=true := by decide +kernel
theorem fusedMap3909swap_checked : acceptsGraphIso
    (fused (graph core3909) (root 8) 4 1) DegreeTwoThreeSpectrum4406.graph fusedMap3909swap=true := by decide +kernel
theorem certified3909swap : Certified (graph core3909) (root 8) 4 1 :=
  of_native_maps core3909 DegreeTwoThreeSpectrum4797.graph DegreeTwoThreeSpectrum4406.graph
    sourceMap3909swap fusedMap3909swap sourceMap3909swap_checked fusedMap3909swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3909
#print axioms sourceMap3909swap_checked
#print axioms fusedMap3909swap_checked
#print axioms certified3909swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
