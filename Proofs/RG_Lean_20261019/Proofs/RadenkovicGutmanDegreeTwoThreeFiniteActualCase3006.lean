/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3006 : Family 10 := level10.get ⟨1580,by decide⟩
def sourceMap3006 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3006 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3006_checked : acceptsGraphIso
    (source (graph core3006) (root 10) 0 4) DegreeTwoThreeSpectrum7118.graph sourceMap3006=true := by decide +kernel
theorem fusedMap3006_checked : acceptsGraphIso
    (fused (graph core3006) (root 10) 0 4) DegreeTwoThreeSpectrum6063.graph fusedMap3006=true := by decide +kernel
theorem certified3006 : Certified (graph core3006) (root 10) 0 4 :=
  of_native_maps core3006 DegreeTwoThreeSpectrum7118.graph DegreeTwoThreeSpectrum6063.graph
    sourceMap3006 fusedMap3006 sourceMap3006_checked fusedMap3006_checked
    DegreeTwoThreeFiniteComparisons.comparison3006
#print axioms sourceMap3006_checked
#print axioms fusedMap3006_checked
#print axioms certified3006
def sourceMap3006swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3006swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3006swap_checked : acceptsGraphIso
    (source (graph core3006) (root 10) 4 0) DegreeTwoThreeSpectrum7118.graph sourceMap3006swap=true := by decide +kernel
theorem fusedMap3006swap_checked : acceptsGraphIso
    (fused (graph core3006) (root 10) 4 0) DegreeTwoThreeSpectrum6063.graph fusedMap3006swap=true := by decide +kernel
theorem certified3006swap : Certified (graph core3006) (root 10) 4 0 :=
  of_native_maps core3006 DegreeTwoThreeSpectrum7118.graph DegreeTwoThreeSpectrum6063.graph
    sourceMap3006swap fusedMap3006swap sourceMap3006swap_checked fusedMap3006swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3006
#print axioms sourceMap3006swap_checked
#print axioms fusedMap3006swap_checked
#print axioms certified3006swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
