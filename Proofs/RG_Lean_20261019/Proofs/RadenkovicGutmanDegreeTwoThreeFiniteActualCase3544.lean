/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3544 : Family 8 := level8.get ⟨31,by decide⟩
def sourceMap3544 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3544 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3544_checked : acceptsGraphIso
    (source (graph core3544) (root 8) 0 6) DegreeTwoThreeSpectrum5117.graph sourceMap3544=true := by decide +kernel
theorem fusedMap3544_checked : acceptsGraphIso
    (fused (graph core3544) (root 8) 0 6) DegreeTwoThreeSpectrum5119.graph fusedMap3544=true := by decide +kernel
theorem certified3544 : Certified (graph core3544) (root 8) 0 6 :=
  of_native_maps core3544 DegreeTwoThreeSpectrum5117.graph DegreeTwoThreeSpectrum5119.graph
    sourceMap3544 fusedMap3544 sourceMap3544_checked fusedMap3544_checked
    DegreeTwoThreeFiniteComparisons.comparison3544
#print axioms sourceMap3544_checked
#print axioms fusedMap3544_checked
#print axioms certified3544
def sourceMap3544swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,16,9] (sourceLabel 8 6 0 v)
def fusedMap3544swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3544swap_checked : acceptsGraphIso
    (source (graph core3544) (root 8) 6 0) DegreeTwoThreeSpectrum5117.graph sourceMap3544swap=true := by decide +kernel
theorem fusedMap3544swap_checked : acceptsGraphIso
    (fused (graph core3544) (root 8) 6 0) DegreeTwoThreeSpectrum5119.graph fusedMap3544swap=true := by decide +kernel
theorem certified3544swap : Certified (graph core3544) (root 8) 6 0 :=
  of_native_maps core3544 DegreeTwoThreeSpectrum5117.graph DegreeTwoThreeSpectrum5119.graph
    sourceMap3544swap fusedMap3544swap sourceMap3544swap_checked fusedMap3544swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3544
#print axioms sourceMap3544swap_checked
#print axioms fusedMap3544swap_checked
#print axioms certified3544swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
