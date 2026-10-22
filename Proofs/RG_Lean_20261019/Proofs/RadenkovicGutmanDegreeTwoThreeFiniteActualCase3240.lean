/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3240 : Family 9 := level9.get ⟨33,by decide⟩
def sourceMap3240 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3240 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,16,9,10,11,12,13,14,15] (fusedLabel 9 0 5 v)
theorem sourceMap3240_checked : acceptsGraphIso
    (source (graph core3240) (root 9) 0 5) DegreeTwoThreeSpectrum5103.graph sourceMap3240=true := by decide +kernel
theorem fusedMap3240_checked : acceptsGraphIso
    (fused (graph core3240) (root 9) 0 5) DegreeTwoThreeSpectrum5105.graph fusedMap3240=true := by decide +kernel
theorem certified3240 : Certified (graph core3240) (root 9) 0 5 :=
  of_native_maps core3240 DegreeTwoThreeSpectrum5103.graph DegreeTwoThreeSpectrum5105.graph
    sourceMap3240 fusedMap3240 sourceMap3240_checked fusedMap3240_checked
    DegreeTwoThreeFiniteComparisons.comparison3240
#print axioms sourceMap3240_checked
#print axioms fusedMap3240_checked
#print axioms certified3240
def sourceMap3240swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3240swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,16,9,10,11,12,13,14,15] (fusedLabel 9 5 0 v)
theorem sourceMap3240swap_checked : acceptsGraphIso
    (source (graph core3240) (root 9) 5 0) DegreeTwoThreeSpectrum5103.graph sourceMap3240swap=true := by decide +kernel
theorem fusedMap3240swap_checked : acceptsGraphIso
    (fused (graph core3240) (root 9) 5 0) DegreeTwoThreeSpectrum5105.graph fusedMap3240swap=true := by decide +kernel
theorem certified3240swap : Certified (graph core3240) (root 9) 5 0 :=
  of_native_maps core3240 DegreeTwoThreeSpectrum5103.graph DegreeTwoThreeSpectrum5105.graph
    sourceMap3240swap fusedMap3240swap sourceMap3240swap_checked fusedMap3240swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3240
#print axioms sourceMap3240swap_checked
#print axioms fusedMap3240swap_checked
#print axioms certified3240swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
