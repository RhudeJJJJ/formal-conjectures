/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2677 : Family 10 := level10.get ⟨757,by decide⟩
def sourceMap2677 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2677 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2677_checked : acceptsGraphIso
    (source (graph core2677) (root 10) 0 4) DegreeTwoThreeSpectrum6667.graph sourceMap2677=true := by decide +kernel
theorem fusedMap2677_checked : acceptsGraphIso
    (fused (graph core2677) (root 10) 0 4) DegreeTwoThreeSpectrum5524.graph fusedMap2677=true := by decide +kernel
theorem certified2677 : Certified (graph core2677) (root 10) 0 4 :=
  of_native_maps core2677 DegreeTwoThreeSpectrum6667.graph DegreeTwoThreeSpectrum5524.graph
    sourceMap2677 fusedMap2677 sourceMap2677_checked fusedMap2677_checked
    DegreeTwoThreeFiniteComparisons.comparison2677
#print axioms sourceMap2677_checked
#print axioms fusedMap2677_checked
#print axioms certified2677
def sourceMap2677swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2677swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2677swap_checked : acceptsGraphIso
    (source (graph core2677) (root 10) 4 0) DegreeTwoThreeSpectrum6667.graph sourceMap2677swap=true := by decide +kernel
theorem fusedMap2677swap_checked : acceptsGraphIso
    (fused (graph core2677) (root 10) 4 0) DegreeTwoThreeSpectrum5524.graph fusedMap2677swap=true := by decide +kernel
theorem certified2677swap : Certified (graph core2677) (root 10) 4 0 :=
  of_native_maps core2677 DegreeTwoThreeSpectrum6667.graph DegreeTwoThreeSpectrum5524.graph
    sourceMap2677swap fusedMap2677swap sourceMap2677swap_checked fusedMap2677swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2677
#print axioms sourceMap2677swap_checked
#print axioms fusedMap2677swap_checked
#print axioms certified2677swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
