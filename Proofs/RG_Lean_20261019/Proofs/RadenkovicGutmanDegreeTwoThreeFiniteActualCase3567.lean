/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3567 : Family 8 := level8.get ⟨105,by decide⟩
def sourceMap3567 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3567 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3567_checked : acceptsGraphIso
    (source (graph core3567) (root 8) 0 6) DegreeTwoThreeSpectrum5193.graph sourceMap3567=true := by decide +kernel
theorem fusedMap3567_checked : acceptsGraphIso
    (fused (graph core3567) (root 8) 0 6) DegreeTwoThreeSpectrum5195.graph fusedMap3567=true := by decide +kernel
theorem certified3567 : Certified (graph core3567) (root 8) 0 6 :=
  of_native_maps core3567 DegreeTwoThreeSpectrum5193.graph DegreeTwoThreeSpectrum5195.graph
    sourceMap3567 fusedMap3567 sourceMap3567_checked fusedMap3567_checked
    DegreeTwoThreeFiniteComparisons.comparison3567
#print axioms sourceMap3567_checked
#print axioms fusedMap3567_checked
#print axioms certified3567
def sourceMap3567swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3567swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3567swap_checked : acceptsGraphIso
    (source (graph core3567) (root 8) 6 0) DegreeTwoThreeSpectrum5193.graph sourceMap3567swap=true := by decide +kernel
theorem fusedMap3567swap_checked : acceptsGraphIso
    (fused (graph core3567) (root 8) 6 0) DegreeTwoThreeSpectrum5195.graph fusedMap3567swap=true := by decide +kernel
theorem certified3567swap : Certified (graph core3567) (root 8) 6 0 :=
  of_native_maps core3567 DegreeTwoThreeSpectrum5193.graph DegreeTwoThreeSpectrum5195.graph
    sourceMap3567swap fusedMap3567swap sourceMap3567swap_checked fusedMap3567swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3567
#print axioms sourceMap3567swap_checked
#print axioms fusedMap3567swap_checked
#print axioms certified3567swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
