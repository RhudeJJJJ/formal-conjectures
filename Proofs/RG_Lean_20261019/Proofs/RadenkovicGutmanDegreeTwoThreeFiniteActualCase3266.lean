/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3266 : Family 9 := level9.get ⟨130,by decide⟩
def sourceMap3266 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3266 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3266_checked : acceptsGraphIso
    (source (graph core3266) (root 9) 0 5) DegreeTwoThreeSpectrum5949.graph sourceMap3266=true := by decide +kernel
theorem fusedMap3266_checked : acceptsGraphIso
    (fused (graph core3266) (root 9) 0 5) DegreeTwoThreeSpectrum5112.graph fusedMap3266=true := by decide +kernel
theorem certified3266 : Certified (graph core3266) (root 9) 0 5 :=
  of_native_maps core3266 DegreeTwoThreeSpectrum5949.graph DegreeTwoThreeSpectrum5112.graph
    sourceMap3266 fusedMap3266 sourceMap3266_checked fusedMap3266_checked
    DegreeTwoThreeFiniteComparisons.comparison3266
#print axioms sourceMap3266_checked
#print axioms fusedMap3266_checked
#print axioms certified3266
def sourceMap3266swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3266swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3266swap_checked : acceptsGraphIso
    (source (graph core3266) (root 9) 5 0) DegreeTwoThreeSpectrum5949.graph sourceMap3266swap=true := by decide +kernel
theorem fusedMap3266swap_checked : acceptsGraphIso
    (fused (graph core3266) (root 9) 5 0) DegreeTwoThreeSpectrum5112.graph fusedMap3266swap=true := by decide +kernel
theorem certified3266swap : Certified (graph core3266) (root 9) 5 0 :=
  of_native_maps core3266 DegreeTwoThreeSpectrum5949.graph DegreeTwoThreeSpectrum5112.graph
    sourceMap3266swap fusedMap3266swap sourceMap3266swap_checked fusedMap3266swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3266
#print axioms sourceMap3266swap_checked
#print axioms fusedMap3266swap_checked
#print axioms certified3266swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
