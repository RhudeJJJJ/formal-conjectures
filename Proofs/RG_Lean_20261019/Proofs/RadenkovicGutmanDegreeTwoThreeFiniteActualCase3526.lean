/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3526 : Family 7 := level7.get ⟨75,by decide⟩
def sourceMap3526 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3526 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3526_checked : acceptsGraphIso
    (source (graph core3526) (root 7) 0 6) DegreeTwoThreeSpectrum4311.graph sourceMap3526=true := by decide +kernel
theorem fusedMap3526_checked : acceptsGraphIso
    (fused (graph core3526) (root 7) 0 6) DegreeTwoThreeSpectrum3927.graph fusedMap3526=true := by decide +kernel
theorem certified3526 : Certified (graph core3526) (root 7) 0 6 :=
  of_native_maps core3526 DegreeTwoThreeSpectrum4311.graph DegreeTwoThreeSpectrum3927.graph
    sourceMap3526 fusedMap3526 sourceMap3526_checked fusedMap3526_checked
    DegreeTwoThreeFiniteComparisons.comparison3526
#print axioms sourceMap3526_checked
#print axioms fusedMap3526_checked
#print axioms certified3526
def sourceMap3526swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,10] (sourceLabel 7 6 0 v)
def fusedMap3526swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3526swap_checked : acceptsGraphIso
    (source (graph core3526) (root 7) 6 0) DegreeTwoThreeSpectrum4311.graph sourceMap3526swap=true := by decide +kernel
theorem fusedMap3526swap_checked : acceptsGraphIso
    (fused (graph core3526) (root 7) 6 0) DegreeTwoThreeSpectrum3927.graph fusedMap3526swap=true := by decide +kernel
theorem certified3526swap : Certified (graph core3526) (root 7) 6 0 :=
  of_native_maps core3526 DegreeTwoThreeSpectrum4311.graph DegreeTwoThreeSpectrum3927.graph
    sourceMap3526swap fusedMap3526swap sourceMap3526swap_checked fusedMap3526swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3526
#print axioms sourceMap3526swap_checked
#print axioms fusedMap3526swap_checked
#print axioms certified3526swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
