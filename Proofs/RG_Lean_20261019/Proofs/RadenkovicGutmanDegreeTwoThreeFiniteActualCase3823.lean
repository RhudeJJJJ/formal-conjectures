/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3823 : Family 7 := level7.get ⟨95,by decide⟩
def sourceMap3823 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3823 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3823_checked : acceptsGraphIso
    (source (graph core3823) (root 7) 1 4) DegreeTwoThreeSpectrum3641.graph sourceMap3823=true := by decide +kernel
theorem fusedMap3823_checked : acceptsGraphIso
    (fused (graph core3823) (root 7) 1 4) DegreeTwoThreeSpectrum2829.graph fusedMap3823=true := by decide +kernel
theorem certified3823 : Certified (graph core3823) (root 7) 1 4 :=
  of_native_maps core3823 DegreeTwoThreeSpectrum3641.graph DegreeTwoThreeSpectrum2829.graph
    sourceMap3823 fusedMap3823 sourceMap3823_checked fusedMap3823_checked
    DegreeTwoThreeFiniteComparisons.comparison3823
#print axioms sourceMap3823_checked
#print axioms fusedMap3823_checked
#print axioms certified3823
def sourceMap3823swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,9,10] (sourceLabel 7 4 1 v)
def fusedMap3823swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3823swap_checked : acceptsGraphIso
    (source (graph core3823) (root 7) 4 1) DegreeTwoThreeSpectrum3641.graph sourceMap3823swap=true := by decide +kernel
theorem fusedMap3823swap_checked : acceptsGraphIso
    (fused (graph core3823) (root 7) 4 1) DegreeTwoThreeSpectrum2829.graph fusedMap3823swap=true := by decide +kernel
theorem certified3823swap : Certified (graph core3823) (root 7) 4 1 :=
  of_native_maps core3823 DegreeTwoThreeSpectrum3641.graph DegreeTwoThreeSpectrum2829.graph
    sourceMap3823swap fusedMap3823swap sourceMap3823swap_checked fusedMap3823swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3823
#print axioms sourceMap3823swap_checked
#print axioms fusedMap3823swap_checked
#print axioms certified3823swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
