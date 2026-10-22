/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2489 : Family 10 := level10.get ⟨171,by decide⟩
def sourceMap2489 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,7,8,2,3,4,5,6] (sourceLabel 10 0 4 v)
def fusedMap2489 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2489_checked : acceptsGraphIso
    (source (graph core2489) (root 10) 0 4) DegreeTwoThreeSpectrum5946.graph sourceMap2489=true := by decide +kernel
theorem fusedMap2489_checked : acceptsGraphIso
    (fused (graph core2489) (root 10) 0 4) DegreeTwoThreeSpectrum5114.graph fusedMap2489=true := by decide +kernel
theorem certified2489 : Certified (graph core2489) (root 10) 0 4 :=
  of_native_maps core2489 DegreeTwoThreeSpectrum5946.graph DegreeTwoThreeSpectrum5114.graph
    sourceMap2489 fusedMap2489 sourceMap2489_checked fusedMap2489_checked
    DegreeTwoThreeFiniteComparisons.comparison2489
#print axioms sourceMap2489_checked
#print axioms fusedMap2489_checked
#print axioms certified2489
def sourceMap2489swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,7,2,3,4,5,6,8] (sourceLabel 10 4 0 v)
def fusedMap2489swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2489swap_checked : acceptsGraphIso
    (source (graph core2489) (root 10) 4 0) DegreeTwoThreeSpectrum5946.graph sourceMap2489swap=true := by decide +kernel
theorem fusedMap2489swap_checked : acceptsGraphIso
    (fused (graph core2489) (root 10) 4 0) DegreeTwoThreeSpectrum5114.graph fusedMap2489swap=true := by decide +kernel
theorem certified2489swap : Certified (graph core2489) (root 10) 4 0 :=
  of_native_maps core2489 DegreeTwoThreeSpectrum5946.graph DegreeTwoThreeSpectrum5114.graph
    sourceMap2489swap fusedMap2489swap sourceMap2489swap_checked fusedMap2489swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2489
#print axioms sourceMap2489swap_checked
#print axioms fusedMap2489swap_checked
#print axioms certified2489swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
