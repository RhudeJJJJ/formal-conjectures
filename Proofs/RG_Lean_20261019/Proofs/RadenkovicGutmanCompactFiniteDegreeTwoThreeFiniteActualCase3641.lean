/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3641 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap3641 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (sourceLabel 5 0 7 v)
def fusedMap3641 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 0 7 v)
theorem sourceMap3641_checked : acceptsGraphIso
    (source (graph core3641) (root 5) 0 7) DegreeTwoThreeSpectrum2329.graph sourceMap3641=true := by decide +kernel
theorem fusedMap3641_checked : acceptsGraphIso
    (fused (graph core3641) (root 5) 0 7) DegreeTwoThreeSpectrum2333.graph fusedMap3641=true := by decide +kernel
theorem certified3641 : Certified (graph core3641) (root 5) 0 7 :=
  of_native_maps core3641 DegreeTwoThreeSpectrum2329.graph DegreeTwoThreeSpectrum2333.graph
    sourceMap3641 fusedMap3641 sourceMap3641_checked fusedMap3641_checked
    DegreeTwoThreeFiniteComparisons.comparison3641
#print axioms sourceMap3641_checked
#print axioms fusedMap3641_checked
#print axioms certified3641
def sourceMap3641swap : (Vertices 5 ⊕ Fin 8 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,1,0,9,10,11,12,13,14,8] (sourceLabel 5 7 0 v)
def fusedMap3641swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 7 0 v)
theorem sourceMap3641swap_checked : acceptsGraphIso
    (source (graph core3641) (root 5) 7 0) DegreeTwoThreeSpectrum2329.graph sourceMap3641swap=true := by decide +kernel
theorem fusedMap3641swap_checked : acceptsGraphIso
    (fused (graph core3641) (root 5) 7 0) DegreeTwoThreeSpectrum2333.graph fusedMap3641swap=true := by decide +kernel
theorem certified3641swap : Certified (graph core3641) (root 5) 7 0 :=
  of_native_maps core3641 DegreeTwoThreeSpectrum2329.graph DegreeTwoThreeSpectrum2333.graph
    sourceMap3641swap fusedMap3641swap sourceMap3641swap_checked fusedMap3641swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3641
#print axioms sourceMap3641swap_checked
#print axioms fusedMap3641swap_checked
#print axioms certified3641swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
