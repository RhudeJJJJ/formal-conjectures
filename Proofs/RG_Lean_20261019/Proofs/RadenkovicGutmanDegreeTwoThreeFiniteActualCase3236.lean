/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3236 : Family 9 := level9.get ⟨8,by decide⟩
def sourceMap3236 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 9 0 5 v)
def fusedMap3236 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,9,10,11,12,13,14,15,16,8,1,2,3,4,5,6,7] (fusedLabel 9 0 5 v)
theorem sourceMap3236_checked : acceptsGraphIso
    (source (graph core3236) (root 9) 0 5) DegreeTwoThreeSpectrum5130.graph sourceMap3236=true := by decide +kernel
theorem fusedMap3236_checked : acceptsGraphIso
    (fused (graph core3236) (root 9) 0 5) DegreeTwoThreeSpectrum4965.graph fusedMap3236=true := by decide +kernel
theorem certified3236 : Certified (graph core3236) (root 9) 0 5 :=
  of_native_maps core3236 DegreeTwoThreeSpectrum5130.graph DegreeTwoThreeSpectrum4965.graph
    sourceMap3236 fusedMap3236 sourceMap3236_checked fusedMap3236_checked
    DegreeTwoThreeFiniteComparisons.comparison3236
#print axioms sourceMap3236_checked
#print axioms fusedMap3236_checked
#print axioms certified3236
def sourceMap3236swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,2,3,4,5,6,7,9] (sourceLabel 9 5 0 v)
def fusedMap3236swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,9,10,11,12,13,14,15,16,8,1,2,3,4,5,6,7] (fusedLabel 9 5 0 v)
theorem sourceMap3236swap_checked : acceptsGraphIso
    (source (graph core3236) (root 9) 5 0) DegreeTwoThreeSpectrum5130.graph sourceMap3236swap=true := by decide +kernel
theorem fusedMap3236swap_checked : acceptsGraphIso
    (fused (graph core3236) (root 9) 5 0) DegreeTwoThreeSpectrum4965.graph fusedMap3236swap=true := by decide +kernel
theorem certified3236swap : Certified (graph core3236) (root 9) 5 0 :=
  of_native_maps core3236 DegreeTwoThreeSpectrum5130.graph DegreeTwoThreeSpectrum4965.graph
    sourceMap3236swap fusedMap3236swap sourceMap3236swap_checked fusedMap3236swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3236
#print axioms sourceMap3236swap_checked
#print axioms fusedMap3236swap_checked
#print axioms certified3236swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
