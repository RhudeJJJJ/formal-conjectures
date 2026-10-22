/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3282 : Family 9 := level9.get ⟨184,by decide⟩
def sourceMap3282 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3282 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3282_checked : acceptsGraphIso
    (source (graph core3282) (root 9) 0 5) DegreeTwoThreeSpectrum5347.graph sourceMap3282=true := by decide +kernel
theorem fusedMap3282_checked : acceptsGraphIso
    (fused (graph core3282) (root 9) 0 5) DegreeTwoThreeSpectrum5348.graph fusedMap3282=true := by decide +kernel
theorem certified3282 : Certified (graph core3282) (root 9) 0 5 :=
  of_native_maps core3282 DegreeTwoThreeSpectrum5347.graph DegreeTwoThreeSpectrum5348.graph
    sourceMap3282 fusedMap3282 sourceMap3282_checked fusedMap3282_checked
    DegreeTwoThreeFiniteComparisons.comparison3282
#print axioms sourceMap3282_checked
#print axioms fusedMap3282_checked
#print axioms certified3282
def sourceMap3282swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3282swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3282swap_checked : acceptsGraphIso
    (source (graph core3282) (root 9) 5 0) DegreeTwoThreeSpectrum5347.graph sourceMap3282swap=true := by decide +kernel
theorem fusedMap3282swap_checked : acceptsGraphIso
    (fused (graph core3282) (root 9) 5 0) DegreeTwoThreeSpectrum5348.graph fusedMap3282swap=true := by decide +kernel
theorem certified3282swap : Certified (graph core3282) (root 9) 5 0 :=
  of_native_maps core3282 DegreeTwoThreeSpectrum5347.graph DegreeTwoThreeSpectrum5348.graph
    sourceMap3282swap fusedMap3282swap sourceMap3282swap_checked fusedMap3282swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3282
#print axioms sourceMap3282swap_checked
#print axioms fusedMap3282swap_checked
#print axioms certified3282swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
