/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3548 : Family 8 := level8.get ⟨47,by decide⟩
def sourceMap3548 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3548 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3548_checked : acceptsGraphIso
    (source (graph core3548) (root 8) 0 6) DegreeTwoThreeSpectrum5355.graph sourceMap3548=true := by decide +kernel
theorem fusedMap3548_checked : acceptsGraphIso
    (fused (graph core3548) (root 8) 0 6) DegreeTwoThreeSpectrum4984.graph fusedMap3548=true := by decide +kernel
theorem certified3548 : Certified (graph core3548) (root 8) 0 6 :=
  of_native_maps core3548 DegreeTwoThreeSpectrum5355.graph DegreeTwoThreeSpectrum4984.graph
    sourceMap3548 fusedMap3548 sourceMap3548_checked fusedMap3548_checked
    DegreeTwoThreeFiniteComparisons.comparison3548
#print axioms sourceMap3548_checked
#print axioms fusedMap3548_checked
#print axioms certified3548
def sourceMap3548swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3548swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3548swap_checked : acceptsGraphIso
    (source (graph core3548) (root 8) 6 0) DegreeTwoThreeSpectrum5355.graph sourceMap3548swap=true := by decide +kernel
theorem fusedMap3548swap_checked : acceptsGraphIso
    (fused (graph core3548) (root 8) 6 0) DegreeTwoThreeSpectrum4984.graph fusedMap3548swap=true := by decide +kernel
theorem certified3548swap : Certified (graph core3548) (root 8) 6 0 :=
  of_native_maps core3548 DegreeTwoThreeSpectrum5355.graph DegreeTwoThreeSpectrum4984.graph
    sourceMap3548swap fusedMap3548swap sourceMap3548swap_checked fusedMap3548swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3548
#print axioms sourceMap3548swap_checked
#print axioms fusedMap3548swap_checked
#print axioms certified3548swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
