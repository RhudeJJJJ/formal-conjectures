/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2743 : Family 10 := level10.get ⟨934,by decide⟩
def sourceMap2743 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2743 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2743_checked : acceptsGraphIso
    (source (graph core2743) (root 10) 0 4) DegreeTwoThreeSpectrum7014.graph sourceMap2743=true := by decide +kernel
theorem fusedMap2743_checked : acceptsGraphIso
    (fused (graph core2743) (root 10) 0 4) DegreeTwoThreeSpectrum5829.graph fusedMap2743=true := by decide +kernel
theorem certified2743 : Certified (graph core2743) (root 10) 0 4 :=
  of_native_maps core2743 DegreeTwoThreeSpectrum7014.graph DegreeTwoThreeSpectrum5829.graph
    sourceMap2743 fusedMap2743 sourceMap2743_checked fusedMap2743_checked
    DegreeTwoThreeFiniteComparisons.comparison2743
#print axioms sourceMap2743_checked
#print axioms fusedMap2743_checked
#print axioms certified2743
def sourceMap2743swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2743swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2743swap_checked : acceptsGraphIso
    (source (graph core2743) (root 10) 4 0) DegreeTwoThreeSpectrum7014.graph sourceMap2743swap=true := by decide +kernel
theorem fusedMap2743swap_checked : acceptsGraphIso
    (fused (graph core2743) (root 10) 4 0) DegreeTwoThreeSpectrum5829.graph fusedMap2743swap=true := by decide +kernel
theorem certified2743swap : Certified (graph core2743) (root 10) 4 0 :=
  of_native_maps core2743 DegreeTwoThreeSpectrum7014.graph DegreeTwoThreeSpectrum5829.graph
    sourceMap2743swap fusedMap2743swap sourceMap2743swap_checked fusedMap2743swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2743
#print axioms sourceMap2743swap_checked
#print axioms fusedMap2743swap_checked
#print axioms certified2743swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
