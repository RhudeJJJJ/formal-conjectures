/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3489 : Family 6 := level6.get ⟨16,by decide⟩
def sourceMap3489 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (sourceLabel 6 0 6 v)
def fusedMap3489 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 0 6 v)
theorem sourceMap3489_checked : acceptsGraphIso
    (source (graph core3489) (root 6) 0 6) DegreeTwoThreeSpectrum2395.graph sourceMap3489=true := by decide +kernel
theorem fusedMap3489_checked : acceptsGraphIso
    (fused (graph core3489) (root 6) 0 6) DegreeTwoThreeSpectrum2398.graph fusedMap3489=true := by decide +kernel
theorem certified3489 : Certified (graph core3489) (root 6) 0 6 :=
  of_native_maps core3489 DegreeTwoThreeSpectrum2395.graph DegreeTwoThreeSpectrum2398.graph
    sourceMap3489 fusedMap3489 sourceMap3489_checked fusedMap3489_checked
    DegreeTwoThreeFiniteComparisons.comparison3489
#print axioms sourceMap3489_checked
#print axioms fusedMap3489_checked
#print axioms certified3489
def sourceMap3489swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,13,14,8] (sourceLabel 6 6 0 v)
def fusedMap3489swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 6 0 v)
theorem sourceMap3489swap_checked : acceptsGraphIso
    (source (graph core3489) (root 6) 6 0) DegreeTwoThreeSpectrum2395.graph sourceMap3489swap=true := by decide +kernel
theorem fusedMap3489swap_checked : acceptsGraphIso
    (fused (graph core3489) (root 6) 6 0) DegreeTwoThreeSpectrum2398.graph fusedMap3489swap=true := by decide +kernel
theorem certified3489swap : Certified (graph core3489) (root 6) 6 0 :=
  of_native_maps core3489 DegreeTwoThreeSpectrum2395.graph DegreeTwoThreeSpectrum2398.graph
    sourceMap3489swap fusedMap3489swap sourceMap3489swap_checked fusedMap3489swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3489
#print axioms sourceMap3489swap_checked
#print axioms fusedMap3489swap_checked
#print axioms certified3489swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
