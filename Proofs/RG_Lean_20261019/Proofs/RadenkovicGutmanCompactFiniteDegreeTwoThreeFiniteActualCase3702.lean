/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3702 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap3702 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (sourceLabel 4 0 8 v)
def fusedMap3702 : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14] (fusedLabel 4 0 8 v)
theorem sourceMap3702_checked : acceptsGraphIso
    (source (graph core3702) (root 4) 0 8) DegreeTwoThreeSpectrum2322.graph sourceMap3702=true := by decide +kernel
theorem fusedMap3702_checked : acceptsGraphIso
    (fused (graph core3702) (root 4) 0 8) DegreeTwoThreeSpectrum2327.graph fusedMap3702=true := by decide +kernel
theorem certified3702 : Certified (graph core3702) (root 4) 0 8 :=
  of_native_maps core3702 DegreeTwoThreeSpectrum2322.graph DegreeTwoThreeSpectrum2327.graph
    sourceMap3702 fusedMap3702 sourceMap3702_checked fusedMap3702_checked
    DegreeTwoThreeFiniteComparisons.comparison3702
#print axioms sourceMap3702_checked
#print axioms fusedMap3702_checked
#print axioms certified3702
def sourceMap3702swap : (Vertices 4 ⊕ Fin 9 ⊕ Fin 1) → Fin 15 :=
  fun v => ![3,4,5,6,7,2,1,0,9,10,11,12,13,14,8] (sourceLabel 4 8 0 v)
def fusedMap3702swap : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14] (fusedLabel 4 8 0 v)
theorem sourceMap3702swap_checked : acceptsGraphIso
    (source (graph core3702) (root 4) 8 0) DegreeTwoThreeSpectrum2322.graph sourceMap3702swap=true := by decide +kernel
theorem fusedMap3702swap_checked : acceptsGraphIso
    (fused (graph core3702) (root 4) 8 0) DegreeTwoThreeSpectrum2327.graph fusedMap3702swap=true := by decide +kernel
theorem certified3702swap : Certified (graph core3702) (root 4) 8 0 :=
  of_native_maps core3702 DegreeTwoThreeSpectrum2322.graph DegreeTwoThreeSpectrum2327.graph
    sourceMap3702swap fusedMap3702swap sourceMap3702swap_checked fusedMap3702swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3702
#print axioms sourceMap3702swap_checked
#print axioms fusedMap3702swap_checked
#print axioms certified3702swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
