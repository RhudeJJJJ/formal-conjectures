/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3701 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap3701 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (sourceLabel 4 0 8 v)
def fusedMap3701 : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13,14] (fusedLabel 4 0 8 v)
theorem sourceMap3701_checked : acceptsGraphIso
    (source (graph core3701) (root 4) 0 8) DegreeTwoThreeSpectrum2393.graph sourceMap3701=true := by decide +kernel
theorem fusedMap3701_checked : acceptsGraphIso
    (fused (graph core3701) (root 4) 0 8) DegreeTwoThreeSpectrum2311.graph fusedMap3701=true := by decide +kernel
theorem certified3701 : Certified (graph core3701) (root 4) 0 8 :=
  of_native_maps core3701 DegreeTwoThreeSpectrum2393.graph DegreeTwoThreeSpectrum2311.graph
    sourceMap3701 fusedMap3701 sourceMap3701_checked fusedMap3701_checked
    DegreeTwoThreeFiniteComparisons.comparison3701
#print axioms sourceMap3701_checked
#print axioms fusedMap3701_checked
#print axioms certified3701
def sourceMap3701swap : (Vertices 4 ⊕ Fin 9 ⊕ Fin 1) → Fin 15 :=
  fun v => ![3,4,5,6,7,2,1,0,9,10,11,12,13,14,8] (sourceLabel 4 8 0 v)
def fusedMap3701swap : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13,14] (fusedLabel 4 8 0 v)
theorem sourceMap3701swap_checked : acceptsGraphIso
    (source (graph core3701) (root 4) 8 0) DegreeTwoThreeSpectrum2393.graph sourceMap3701swap=true := by decide +kernel
theorem fusedMap3701swap_checked : acceptsGraphIso
    (fused (graph core3701) (root 4) 8 0) DegreeTwoThreeSpectrum2311.graph fusedMap3701swap=true := by decide +kernel
theorem certified3701swap : Certified (graph core3701) (root 4) 8 0 :=
  of_native_maps core3701 DegreeTwoThreeSpectrum2393.graph DegreeTwoThreeSpectrum2311.graph
    sourceMap3701swap fusedMap3701swap sourceMap3701swap_checked fusedMap3701swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3701
#print axioms sourceMap3701swap_checked
#print axioms fusedMap3701swap_checked
#print axioms certified3701swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
