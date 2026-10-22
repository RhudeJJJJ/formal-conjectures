/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3597 : Family 8 := level8.get ⟨179,by decide⟩
def sourceMap3597 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3597 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3597_checked : acceptsGraphIso
    (source (graph core3597) (root 8) 0 6) DegreeTwoThreeSpectrum5818.graph sourceMap3597=true := by decide +kernel
theorem fusedMap3597_checked : acceptsGraphIso
    (fused (graph core3597) (root 8) 0 6) DegreeTwoThreeSpectrum5820.graph fusedMap3597=true := by decide +kernel
theorem certified3597 : Certified (graph core3597) (root 8) 0 6 :=
  of_native_maps core3597 DegreeTwoThreeSpectrum5818.graph DegreeTwoThreeSpectrum5820.graph
    sourceMap3597 fusedMap3597 sourceMap3597_checked fusedMap3597_checked
    DegreeTwoThreeFiniteComparisons.comparison3597
#print axioms sourceMap3597_checked
#print axioms fusedMap3597_checked
#print axioms certified3597
def sourceMap3597swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3597swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3597swap_checked : acceptsGraphIso
    (source (graph core3597) (root 8) 6 0) DegreeTwoThreeSpectrum5818.graph sourceMap3597swap=true := by decide +kernel
theorem fusedMap3597swap_checked : acceptsGraphIso
    (fused (graph core3597) (root 8) 6 0) DegreeTwoThreeSpectrum5820.graph fusedMap3597swap=true := by decide +kernel
theorem certified3597swap : Certified (graph core3597) (root 8) 6 0 :=
  of_native_maps core3597 DegreeTwoThreeSpectrum5818.graph DegreeTwoThreeSpectrum5820.graph
    sourceMap3597swap fusedMap3597swap sourceMap3597swap_checked fusedMap3597swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3597
#print axioms sourceMap3597swap_checked
#print axioms fusedMap3597swap_checked
#print axioms certified3597swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
