/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3250 : Family 9 := level9.get ⟨73,by decide⟩
def sourceMap3250 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3250 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3250_checked : acceptsGraphIso
    (source (graph core3250) (root 9) 0 5) DegreeTwoThreeSpectrum5481.graph sourceMap3250=true := by decide +kernel
theorem fusedMap3250_checked : acceptsGraphIso
    (fused (graph core3250) (root 9) 0 5) DegreeTwoThreeSpectrum5012.graph fusedMap3250=true := by decide +kernel
theorem certified3250 : Certified (graph core3250) (root 9) 0 5 :=
  of_native_maps core3250 DegreeTwoThreeSpectrum5481.graph DegreeTwoThreeSpectrum5012.graph
    sourceMap3250 fusedMap3250 sourceMap3250_checked fusedMap3250_checked
    DegreeTwoThreeFiniteComparisons.comparison3250
#print axioms sourceMap3250_checked
#print axioms fusedMap3250_checked
#print axioms certified3250
def sourceMap3250swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3250swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3250swap_checked : acceptsGraphIso
    (source (graph core3250) (root 9) 5 0) DegreeTwoThreeSpectrum5481.graph sourceMap3250swap=true := by decide +kernel
theorem fusedMap3250swap_checked : acceptsGraphIso
    (fused (graph core3250) (root 9) 5 0) DegreeTwoThreeSpectrum5012.graph fusedMap3250swap=true := by decide +kernel
theorem certified3250swap : Certified (graph core3250) (root 9) 5 0 :=
  of_native_maps core3250 DegreeTwoThreeSpectrum5481.graph DegreeTwoThreeSpectrum5012.graph
    sourceMap3250swap fusedMap3250swap sourceMap3250swap_checked fusedMap3250swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3250
#print axioms sourceMap3250swap_checked
#print axioms fusedMap3250swap_checked
#print axioms certified3250swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
