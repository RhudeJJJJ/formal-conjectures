/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2732 : Family 10 := level10.get ⟨906,by decide⟩
def sourceMap2732 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2732 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2732_checked : acceptsGraphIso
    (source (graph core2732) (root 10) 0 4) DegreeTwoThreeSpectrum6982.graph sourceMap2732=true := by decide +kernel
theorem fusedMap2732_checked : acceptsGraphIso
    (fused (graph core2732) (root 10) 0 4) DegreeTwoThreeSpectrum5772.graph fusedMap2732=true := by decide +kernel
theorem certified2732 : Certified (graph core2732) (root 10) 0 4 :=
  of_native_maps core2732 DegreeTwoThreeSpectrum6982.graph DegreeTwoThreeSpectrum5772.graph
    sourceMap2732 fusedMap2732 sourceMap2732_checked fusedMap2732_checked
    DegreeTwoThreeFiniteComparisons.comparison2732
#print axioms sourceMap2732_checked
#print axioms fusedMap2732_checked
#print axioms certified2732
def sourceMap2732swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2732swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2732swap_checked : acceptsGraphIso
    (source (graph core2732) (root 10) 4 0) DegreeTwoThreeSpectrum6982.graph sourceMap2732swap=true := by decide +kernel
theorem fusedMap2732swap_checked : acceptsGraphIso
    (fused (graph core2732) (root 10) 4 0) DegreeTwoThreeSpectrum5772.graph fusedMap2732swap=true := by decide +kernel
theorem certified2732swap : Certified (graph core2732) (root 10) 4 0 :=
  of_native_maps core2732 DegreeTwoThreeSpectrum6982.graph DegreeTwoThreeSpectrum5772.graph
    sourceMap2732swap fusedMap2732swap sourceMap2732swap_checked fusedMap2732swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2732
#print axioms sourceMap2732swap_checked
#print axioms fusedMap2732swap_checked
#print axioms certified2732swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
