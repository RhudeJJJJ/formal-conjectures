/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3871 : Family 8 := level8.get ⟨147,by decide⟩
def sourceMap3871 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3871 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3871_checked : acceptsGraphIso
    (source (graph core3871) (root 8) 1 4) DegreeTwoThreeSpectrum4476.graph sourceMap3871=true := by decide +kernel
theorem fusedMap3871_checked : acceptsGraphIso
    (fused (graph core3871) (root 8) 1 4) DegreeTwoThreeSpectrum4009.graph fusedMap3871=true := by decide +kernel
theorem certified3871 : Certified (graph core3871) (root 8) 1 4 :=
  of_native_maps core3871 DegreeTwoThreeSpectrum4476.graph DegreeTwoThreeSpectrum4009.graph
    sourceMap3871 fusedMap3871 sourceMap3871_checked fusedMap3871_checked
    DegreeTwoThreeFiniteComparisons.comparison3871
#print axioms sourceMap3871_checked
#print axioms fusedMap3871_checked
#print axioms certified3871
def sourceMap3871swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3871swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3871swap_checked : acceptsGraphIso
    (source (graph core3871) (root 8) 4 1) DegreeTwoThreeSpectrum4476.graph sourceMap3871swap=true := by decide +kernel
theorem fusedMap3871swap_checked : acceptsGraphIso
    (fused (graph core3871) (root 8) 4 1) DegreeTwoThreeSpectrum4009.graph fusedMap3871swap=true := by decide +kernel
theorem certified3871swap : Certified (graph core3871) (root 8) 4 1 :=
  of_native_maps core3871 DegreeTwoThreeSpectrum4476.graph DegreeTwoThreeSpectrum4009.graph
    sourceMap3871swap fusedMap3871swap sourceMap3871swap_checked fusedMap3871swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3871
#print axioms sourceMap3871swap_checked
#print axioms fusedMap3871swap_checked
#print axioms certified3871swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
