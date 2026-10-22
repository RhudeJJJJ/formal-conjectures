/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3524 : Family 7 := level7.get ⟨72,by decide⟩
def sourceMap3524 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3524 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3524_checked : acceptsGraphIso
    (source (graph core3524) (root 7) 0 6) DegreeTwoThreeSpectrum4279.graph sourceMap3524=true := by decide +kernel
theorem fusedMap3524_checked : acceptsGraphIso
    (fused (graph core3524) (root 7) 0 6) DegreeTwoThreeSpectrum3919.graph fusedMap3524=true := by decide +kernel
theorem certified3524 : Certified (graph core3524) (root 7) 0 6 :=
  of_native_maps core3524 DegreeTwoThreeSpectrum4279.graph DegreeTwoThreeSpectrum3919.graph
    sourceMap3524 fusedMap3524 sourceMap3524_checked fusedMap3524_checked
    DegreeTwoThreeFiniteComparisons.comparison3524
#print axioms sourceMap3524_checked
#print axioms fusedMap3524_checked
#print axioms certified3524
def sourceMap3524swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,10] (sourceLabel 7 6 0 v)
def fusedMap3524swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3524swap_checked : acceptsGraphIso
    (source (graph core3524) (root 7) 6 0) DegreeTwoThreeSpectrum4279.graph sourceMap3524swap=true := by decide +kernel
theorem fusedMap3524swap_checked : acceptsGraphIso
    (fused (graph core3524) (root 7) 6 0) DegreeTwoThreeSpectrum3919.graph fusedMap3524swap=true := by decide +kernel
theorem certified3524swap : Certified (graph core3524) (root 7) 6 0 :=
  of_native_maps core3524 DegreeTwoThreeSpectrum4279.graph DegreeTwoThreeSpectrum3919.graph
    sourceMap3524swap fusedMap3524swap sourceMap3524swap_checked fusedMap3524swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3524
#print axioms sourceMap3524swap_checked
#print axioms fusedMap3524swap_checked
#print axioms certified3524swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
