/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3740 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap3740 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (sourceLabel 4 0 10 v)
def fusedMap3740 : (Vertices 4 ⊕ Fin 12) → Fin 17 :=
  fun v => ![5,6,7,8,9,4,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 4 0 10 v)
theorem sourceMap3740_checked : acceptsGraphIso
    (source (graph core3740) (root 4) 0 10) DegreeTwoThreeSpectrum4974.graph sourceMap3740=true := by decide +kernel
theorem fusedMap3740_checked : acceptsGraphIso
    (fused (graph core3740) (root 4) 0 10) DegreeTwoThreeSpectrum4980.graph fusedMap3740=true := by decide +kernel
theorem certified3740 : Certified (graph core3740) (root 4) 0 10 :=
  of_native_maps core3740 DegreeTwoThreeSpectrum4974.graph DegreeTwoThreeSpectrum4980.graph
    sourceMap3740 fusedMap3740 sourceMap3740_checked fusedMap3740_checked
    DegreeTwoThreeFiniteComparisons.comparison3740
#print axioms sourceMap3740_checked
#print axioms fusedMap3740_checked
#print axioms certified3740
def sourceMap3740swap : (Vertices 4 ⊕ Fin 11 ⊕ Fin 1) → Fin 17 :=
  fun v => ![4,5,6,7,8,3,2,1,0,10,11,12,13,14,15,16,9] (sourceLabel 4 10 0 v)
def fusedMap3740swap : (Vertices 4 ⊕ Fin 12) → Fin 17 :=
  fun v => ![5,6,7,8,9,4,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 4 10 0 v)
theorem sourceMap3740swap_checked : acceptsGraphIso
    (source (graph core3740) (root 4) 10 0) DegreeTwoThreeSpectrum4974.graph sourceMap3740swap=true := by decide +kernel
theorem fusedMap3740swap_checked : acceptsGraphIso
    (fused (graph core3740) (root 4) 10 0) DegreeTwoThreeSpectrum4980.graph fusedMap3740swap=true := by decide +kernel
theorem certified3740swap : Certified (graph core3740) (root 4) 10 0 :=
  of_native_maps core3740 DegreeTwoThreeSpectrum4974.graph DegreeTwoThreeSpectrum4980.graph
    sourceMap3740swap fusedMap3740swap sourceMap3740swap_checked fusedMap3740swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3740
#print axioms sourceMap3740swap_checked
#print axioms fusedMap3740swap_checked
#print axioms certified3740swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
