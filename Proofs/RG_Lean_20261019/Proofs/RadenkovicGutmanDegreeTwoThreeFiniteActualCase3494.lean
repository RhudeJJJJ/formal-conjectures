/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3494 : Family 6 := level6.get ⟨28,by decide⟩
def sourceMap3494 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (sourceLabel 6 0 6 v)
def fusedMap3494 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 0 6 v)
theorem sourceMap3494_checked : acceptsGraphIso
    (source (graph core3494) (root 6) 0 6) DegreeTwoThreeSpectrum2667.graph sourceMap3494=true := by decide +kernel
theorem fusedMap3494_checked : acceptsGraphIso
    (fused (graph core3494) (root 6) 0 6) DegreeTwoThreeSpectrum2350.graph fusedMap3494=true := by decide +kernel
theorem certified3494 : Certified (graph core3494) (root 6) 0 6 :=
  of_native_maps core3494 DegreeTwoThreeSpectrum2667.graph DegreeTwoThreeSpectrum2350.graph
    sourceMap3494 fusedMap3494 sourceMap3494_checked fusedMap3494_checked
    DegreeTwoThreeFiniteComparisons.comparison3494
#print axioms sourceMap3494_checked
#print axioms fusedMap3494_checked
#print axioms certified3494
def sourceMap3494swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,9] (sourceLabel 6 6 0 v)
def fusedMap3494swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 6 0 v)
theorem sourceMap3494swap_checked : acceptsGraphIso
    (source (graph core3494) (root 6) 6 0) DegreeTwoThreeSpectrum2667.graph sourceMap3494swap=true := by decide +kernel
theorem fusedMap3494swap_checked : acceptsGraphIso
    (fused (graph core3494) (root 6) 6 0) DegreeTwoThreeSpectrum2350.graph fusedMap3494swap=true := by decide +kernel
theorem certified3494swap : Certified (graph core3494) (root 6) 6 0 :=
  of_native_maps core3494 DegreeTwoThreeSpectrum2667.graph DegreeTwoThreeSpectrum2350.graph
    sourceMap3494swap fusedMap3494swap sourceMap3494swap_checked fusedMap3494swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3494
#print axioms sourceMap3494swap_checked
#print axioms fusedMap3494swap_checked
#print axioms certified3494swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
