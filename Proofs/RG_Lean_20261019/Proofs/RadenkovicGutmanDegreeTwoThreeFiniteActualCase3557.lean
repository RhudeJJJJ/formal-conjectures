/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3557 : Family 8 := level8.get ⟨77,by decide⟩
def sourceMap3557 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3557 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3557_checked : acceptsGraphIso
    (source (graph core3557) (root 8) 0 6) DegreeTwoThreeSpectrum5753.graph sourceMap3557=true := by decide +kernel
theorem fusedMap3557_checked : acceptsGraphIso
    (fused (graph core3557) (root 8) 0 6) DegreeTwoThreeSpectrum5057.graph fusedMap3557=true := by decide +kernel
theorem certified3557 : Certified (graph core3557) (root 8) 0 6 :=
  of_native_maps core3557 DegreeTwoThreeSpectrum5753.graph DegreeTwoThreeSpectrum5057.graph
    sourceMap3557 fusedMap3557 sourceMap3557_checked fusedMap3557_checked
    DegreeTwoThreeFiniteComparisons.comparison3557
#print axioms sourceMap3557_checked
#print axioms fusedMap3557_checked
#print axioms certified3557
def sourceMap3557swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3557swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3557swap_checked : acceptsGraphIso
    (source (graph core3557) (root 8) 6 0) DegreeTwoThreeSpectrum5753.graph sourceMap3557swap=true := by decide +kernel
theorem fusedMap3557swap_checked : acceptsGraphIso
    (fused (graph core3557) (root 8) 6 0) DegreeTwoThreeSpectrum5057.graph fusedMap3557swap=true := by decide +kernel
theorem certified3557swap : Certified (graph core3557) (root 8) 6 0 :=
  of_native_maps core3557 DegreeTwoThreeSpectrum5753.graph DegreeTwoThreeSpectrum5057.graph
    sourceMap3557swap fusedMap3557swap sourceMap3557swap_checked fusedMap3557swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3557
#print axioms sourceMap3557swap_checked
#print axioms fusedMap3557swap_checked
#print axioms certified3557swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
