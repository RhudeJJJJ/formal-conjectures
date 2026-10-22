/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3543 : Family 8 := level8.get ⟨28,by decide⟩
def sourceMap3543 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3543 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3543_checked : acceptsGraphIso
    (source (graph core3543) (root 8) 0 6) DegreeTwoThreeSpectrum5098.graph sourceMap3543=true := by decide +kernel
theorem fusedMap3543_checked : acceptsGraphIso
    (fused (graph core3543) (root 8) 0 6) DegreeTwoThreeSpectrum5100.graph fusedMap3543=true := by decide +kernel
theorem certified3543 : Certified (graph core3543) (root 8) 0 6 :=
  of_native_maps core3543 DegreeTwoThreeSpectrum5098.graph DegreeTwoThreeSpectrum5100.graph
    sourceMap3543 fusedMap3543 sourceMap3543_checked fusedMap3543_checked
    DegreeTwoThreeFiniteComparisons.comparison3543
#print axioms sourceMap3543_checked
#print axioms fusedMap3543_checked
#print axioms certified3543
def sourceMap3543swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,16,9] (sourceLabel 8 6 0 v)
def fusedMap3543swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3543swap_checked : acceptsGraphIso
    (source (graph core3543) (root 8) 6 0) DegreeTwoThreeSpectrum5098.graph sourceMap3543swap=true := by decide +kernel
theorem fusedMap3543swap_checked : acceptsGraphIso
    (fused (graph core3543) (root 8) 6 0) DegreeTwoThreeSpectrum5100.graph fusedMap3543swap=true := by decide +kernel
theorem certified3543swap : Certified (graph core3543) (root 8) 6 0 :=
  of_native_maps core3543 DegreeTwoThreeSpectrum5098.graph DegreeTwoThreeSpectrum5100.graph
    sourceMap3543swap fusedMap3543swap sourceMap3543swap_checked fusedMap3543swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3543
#print axioms sourceMap3543swap_checked
#print axioms fusedMap3543swap_checked
#print axioms certified3543swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
