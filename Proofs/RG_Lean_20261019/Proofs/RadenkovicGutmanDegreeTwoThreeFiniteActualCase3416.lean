/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3416 : Family 9 := level9.get ⟨528,by decide⟩
def sourceMap3416 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3416 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3416_checked : acceptsGraphIso
    (source (graph core3416) (root 9) 0 5) DegreeTwoThreeSpectrum7004.graph sourceMap3416=true := by decide +kernel
theorem fusedMap3416_checked : acceptsGraphIso
    (fused (graph core3416) (root 9) 0 5) DegreeTwoThreeSpectrum5822.graph fusedMap3416=true := by decide +kernel
theorem certified3416 : Certified (graph core3416) (root 9) 0 5 :=
  of_native_maps core3416 DegreeTwoThreeSpectrum7004.graph DegreeTwoThreeSpectrum5822.graph
    sourceMap3416 fusedMap3416 sourceMap3416_checked fusedMap3416_checked
    DegreeTwoThreeFiniteComparisons.comparison3416
#print axioms sourceMap3416_checked
#print axioms fusedMap3416_checked
#print axioms certified3416
def sourceMap3416swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3416swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3416swap_checked : acceptsGraphIso
    (source (graph core3416) (root 9) 5 0) DegreeTwoThreeSpectrum7004.graph sourceMap3416swap=true := by decide +kernel
theorem fusedMap3416swap_checked : acceptsGraphIso
    (fused (graph core3416) (root 9) 5 0) DegreeTwoThreeSpectrum5822.graph fusedMap3416swap=true := by decide +kernel
theorem certified3416swap : Certified (graph core3416) (root 9) 5 0 :=
  of_native_maps core3416 DegreeTwoThreeSpectrum7004.graph DegreeTwoThreeSpectrum5822.graph
    sourceMap3416swap fusedMap3416swap sourceMap3416swap_checked fusedMap3416swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3416
#print axioms sourceMap3416swap_checked
#print axioms fusedMap3416swap_checked
#print axioms certified3416swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
