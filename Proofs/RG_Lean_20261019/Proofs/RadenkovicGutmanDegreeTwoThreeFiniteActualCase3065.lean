/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3065 : Family 10 := level10.get ⟨1744,by decide⟩
def sourceMap3065 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3065 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3065_checked : acceptsGraphIso
    (source (graph core3065) (root 10) 0 4) DegreeTwoThreeSpectrum7386.graph sourceMap3065=true := by decide +kernel
theorem fusedMap3065_checked : acceptsGraphIso
    (fused (graph core3065) (root 10) 0 4) DegreeTwoThreeSpectrum6597.graph fusedMap3065=true := by decide +kernel
theorem certified3065 : Certified (graph core3065) (root 10) 0 4 :=
  of_native_maps core3065 DegreeTwoThreeSpectrum7386.graph DegreeTwoThreeSpectrum6597.graph
    sourceMap3065 fusedMap3065 sourceMap3065_checked fusedMap3065_checked
    DegreeTwoThreeFiniteComparisons.comparison3065
#print axioms sourceMap3065_checked
#print axioms fusedMap3065_checked
#print axioms certified3065
def sourceMap3065swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3065swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3065swap_checked : acceptsGraphIso
    (source (graph core3065) (root 10) 4 0) DegreeTwoThreeSpectrum7386.graph sourceMap3065swap=true := by decide +kernel
theorem fusedMap3065swap_checked : acceptsGraphIso
    (fused (graph core3065) (root 10) 4 0) DegreeTwoThreeSpectrum6597.graph fusedMap3065swap=true := by decide +kernel
theorem certified3065swap : Certified (graph core3065) (root 10) 4 0 :=
  of_native_maps core3065 DegreeTwoThreeSpectrum7386.graph DegreeTwoThreeSpectrum6597.graph
    sourceMap3065swap fusedMap3065swap sourceMap3065swap_checked fusedMap3065swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3065
#print axioms sourceMap3065swap_checked
#print axioms fusedMap3065swap_checked
#print axioms certified3065swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
