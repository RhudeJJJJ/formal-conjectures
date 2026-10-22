/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3305 : Family 9 := level9.get ⟨248,by decide⟩
def sourceMap3305 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3305 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3305_checked : acceptsGraphIso
    (source (graph core3305) (root 9) 0 5) DegreeTwoThreeSpectrum5636.graph sourceMap3305=true := by decide +kernel
theorem fusedMap3305_checked : acceptsGraphIso
    (fused (graph core3305) (root 9) 0 5) DegreeTwoThreeSpectrum5637.graph fusedMap3305=true := by decide +kernel
theorem certified3305 : Certified (graph core3305) (root 9) 0 5 :=
  of_native_maps core3305 DegreeTwoThreeSpectrum5636.graph DegreeTwoThreeSpectrum5637.graph
    sourceMap3305 fusedMap3305 sourceMap3305_checked fusedMap3305_checked
    DegreeTwoThreeFiniteComparisons.comparison3305
#print axioms sourceMap3305_checked
#print axioms fusedMap3305_checked
#print axioms certified3305
def sourceMap3305swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3305swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3305swap_checked : acceptsGraphIso
    (source (graph core3305) (root 9) 5 0) DegreeTwoThreeSpectrum5636.graph sourceMap3305swap=true := by decide +kernel
theorem fusedMap3305swap_checked : acceptsGraphIso
    (fused (graph core3305) (root 9) 5 0) DegreeTwoThreeSpectrum5637.graph fusedMap3305swap=true := by decide +kernel
theorem certified3305swap : Certified (graph core3305) (root 9) 5 0 :=
  of_native_maps core3305 DegreeTwoThreeSpectrum5636.graph DegreeTwoThreeSpectrum5637.graph
    sourceMap3305swap fusedMap3305swap sourceMap3305swap_checked fusedMap3305swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3305
#print axioms sourceMap3305swap_checked
#print axioms fusedMap3305swap_checked
#print axioms certified3305swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
