/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3901 : Family 8 := level8.get ⟨216,by decide⟩
def sourceMap3901 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3901 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3901_checked : acceptsGraphIso
    (source (graph core3901) (root 8) 1 4) DegreeTwoThreeSpectrum4740.graph sourceMap3901=true := by decide +kernel
theorem fusedMap3901_checked : acceptsGraphIso
    (fused (graph core3901) (root 8) 1 4) DegreeTwoThreeSpectrum4295.graph fusedMap3901=true := by decide +kernel
theorem certified3901 : Certified (graph core3901) (root 8) 1 4 :=
  of_native_maps core3901 DegreeTwoThreeSpectrum4740.graph DegreeTwoThreeSpectrum4295.graph
    sourceMap3901 fusedMap3901 sourceMap3901_checked fusedMap3901_checked
    DegreeTwoThreeFiniteComparisons.comparison3901
#print axioms sourceMap3901_checked
#print axioms fusedMap3901_checked
#print axioms certified3901
def sourceMap3901swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,12,13,14,15,10,11] (sourceLabel 8 4 1 v)
def fusedMap3901swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3901swap_checked : acceptsGraphIso
    (source (graph core3901) (root 8) 4 1) DegreeTwoThreeSpectrum4740.graph sourceMap3901swap=true := by decide +kernel
theorem fusedMap3901swap_checked : acceptsGraphIso
    (fused (graph core3901) (root 8) 4 1) DegreeTwoThreeSpectrum4295.graph fusedMap3901swap=true := by decide +kernel
theorem certified3901swap : Certified (graph core3901) (root 8) 4 1 :=
  of_native_maps core3901 DegreeTwoThreeSpectrum4740.graph DegreeTwoThreeSpectrum4295.graph
    sourceMap3901swap fusedMap3901swap sourceMap3901swap_checked fusedMap3901swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3901
#print axioms sourceMap3901swap_checked
#print axioms fusedMap3901swap_checked
#print axioms certified3901swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
