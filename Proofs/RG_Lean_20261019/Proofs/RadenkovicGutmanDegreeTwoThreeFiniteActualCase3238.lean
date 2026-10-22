/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3238 : Family 9 := level9.get ⟨22,by decide⟩
def sourceMap3238 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3238 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,16,9,10,11,12,13,14,15] (fusedLabel 9 0 5 v)
theorem sourceMap3238_checked : acceptsGraphIso
    (source (graph core3238) (root 9) 0 5) DegreeTwoThreeSpectrum5045.graph sourceMap3238=true := by decide +kernel
theorem fusedMap3238_checked : acceptsGraphIso
    (fused (graph core3238) (root 9) 0 5) DegreeTwoThreeSpectrum5047.graph fusedMap3238=true := by decide +kernel
theorem certified3238 : Certified (graph core3238) (root 9) 0 5 :=
  of_native_maps core3238 DegreeTwoThreeSpectrum5045.graph DegreeTwoThreeSpectrum5047.graph
    sourceMap3238 fusedMap3238 sourceMap3238_checked fusedMap3238_checked
    DegreeTwoThreeFiniteComparisons.comparison3238
#print axioms sourceMap3238_checked
#print axioms fusedMap3238_checked
#print axioms certified3238
def sourceMap3238swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3238swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,16,9,10,11,12,13,14,15] (fusedLabel 9 5 0 v)
theorem sourceMap3238swap_checked : acceptsGraphIso
    (source (graph core3238) (root 9) 5 0) DegreeTwoThreeSpectrum5045.graph sourceMap3238swap=true := by decide +kernel
theorem fusedMap3238swap_checked : acceptsGraphIso
    (fused (graph core3238) (root 9) 5 0) DegreeTwoThreeSpectrum5047.graph fusedMap3238swap=true := by decide +kernel
theorem certified3238swap : Certified (graph core3238) (root 9) 5 0 :=
  of_native_maps core3238 DegreeTwoThreeSpectrum5045.graph DegreeTwoThreeSpectrum5047.graph
    sourceMap3238swap fusedMap3238swap sourceMap3238swap_checked fusedMap3238swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3238
#print axioms sourceMap3238swap_checked
#print axioms fusedMap3238swap_checked
#print axioms certified3238swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
