/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3612 : Family 8 := level8.get ⟨215,by decide⟩
def sourceMap3612 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3612 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3612_checked : acceptsGraphIso
    (source (graph core3612) (root 8) 0 6) DegreeTwoThreeSpectrum6247.graph sourceMap3612=true := by decide +kernel
theorem fusedMap3612_checked : acceptsGraphIso
    (fused (graph core3612) (root 8) 0 6) DegreeTwoThreeSpectrum5247.graph fusedMap3612=true := by decide +kernel
theorem certified3612 : Certified (graph core3612) (root 8) 0 6 :=
  of_native_maps core3612 DegreeTwoThreeSpectrum6247.graph DegreeTwoThreeSpectrum5247.graph
    sourceMap3612 fusedMap3612 sourceMap3612_checked fusedMap3612_checked
    DegreeTwoThreeFiniteComparisons.comparison3612
#print axioms sourceMap3612_checked
#print axioms fusedMap3612_checked
#print axioms certified3612
def sourceMap3612swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3612swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3612swap_checked : acceptsGraphIso
    (source (graph core3612) (root 8) 6 0) DegreeTwoThreeSpectrum6247.graph sourceMap3612swap=true := by decide +kernel
theorem fusedMap3612swap_checked : acceptsGraphIso
    (fused (graph core3612) (root 8) 6 0) DegreeTwoThreeSpectrum5247.graph fusedMap3612swap=true := by decide +kernel
theorem certified3612swap : Certified (graph core3612) (root 8) 6 0 :=
  of_native_maps core3612 DegreeTwoThreeSpectrum6247.graph DegreeTwoThreeSpectrum5247.graph
    sourceMap3612swap fusedMap3612swap sourceMap3612swap_checked fusedMap3612swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3612
#print axioms sourceMap3612swap_checked
#print axioms fusedMap3612swap_checked
#print axioms certified3612swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
