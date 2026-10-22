/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3389 : Family 9 := level9.get ⟨470,by decide⟩
def sourceMap3389 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3389 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3389_checked : acceptsGraphIso
    (source (graph core3389) (root 9) 0 5) DegreeTwoThreeSpectrum6717.graph sourceMap3389=true := by decide +kernel
theorem fusedMap3389_checked : acceptsGraphIso
    (fused (graph core3389) (root 9) 0 5) DegreeTwoThreeSpectrum5562.graph fusedMap3389=true := by decide +kernel
theorem certified3389 : Certified (graph core3389) (root 9) 0 5 :=
  of_native_maps core3389 DegreeTwoThreeSpectrum6717.graph DegreeTwoThreeSpectrum5562.graph
    sourceMap3389 fusedMap3389 sourceMap3389_checked fusedMap3389_checked
    DegreeTwoThreeFiniteComparisons.comparison3389
#print axioms sourceMap3389_checked
#print axioms fusedMap3389_checked
#print axioms certified3389
def sourceMap3389swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3389swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3389swap_checked : acceptsGraphIso
    (source (graph core3389) (root 9) 5 0) DegreeTwoThreeSpectrum6717.graph sourceMap3389swap=true := by decide +kernel
theorem fusedMap3389swap_checked : acceptsGraphIso
    (fused (graph core3389) (root 9) 5 0) DegreeTwoThreeSpectrum5562.graph fusedMap3389swap=true := by decide +kernel
theorem certified3389swap : Certified (graph core3389) (root 9) 5 0 :=
  of_native_maps core3389 DegreeTwoThreeSpectrum6717.graph DegreeTwoThreeSpectrum5562.graph
    sourceMap3389swap fusedMap3389swap sourceMap3389swap_checked fusedMap3389swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3389
#print axioms sourceMap3389swap_checked
#print axioms fusedMap3389swap_checked
#print axioms certified3389swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
