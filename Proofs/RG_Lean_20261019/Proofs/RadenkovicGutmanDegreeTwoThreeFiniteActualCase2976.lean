/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2976 : Family 10 := level10.get ⟨1497,by decide⟩
def sourceMap2976 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2976 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2976_checked : acceptsGraphIso
    (source (graph core2976) (root 10) 0 4) DegreeTwoThreeSpectrum7000.graph sourceMap2976=true := by decide +kernel
theorem fusedMap2976_checked : acceptsGraphIso
    (fused (graph core2976) (root 10) 0 4) DegreeTwoThreeSpectrum7001.graph fusedMap2976=true := by decide +kernel
theorem certified2976 : Certified (graph core2976) (root 10) 0 4 :=
  of_native_maps core2976 DegreeTwoThreeSpectrum7000.graph DegreeTwoThreeSpectrum7001.graph
    sourceMap2976 fusedMap2976 sourceMap2976_checked fusedMap2976_checked
    DegreeTwoThreeFiniteComparisons.comparison2976
#print axioms sourceMap2976_checked
#print axioms fusedMap2976_checked
#print axioms certified2976
def sourceMap2976swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2976swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2976swap_checked : acceptsGraphIso
    (source (graph core2976) (root 10) 4 0) DegreeTwoThreeSpectrum7000.graph sourceMap2976swap=true := by decide +kernel
theorem fusedMap2976swap_checked : acceptsGraphIso
    (fused (graph core2976) (root 10) 4 0) DegreeTwoThreeSpectrum7001.graph fusedMap2976swap=true := by decide +kernel
theorem certified2976swap : Certified (graph core2976) (root 10) 4 0 :=
  of_native_maps core2976 DegreeTwoThreeSpectrum7000.graph DegreeTwoThreeSpectrum7001.graph
    sourceMap2976swap fusedMap2976swap sourceMap2976swap_checked fusedMap2976swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2976
#print axioms sourceMap2976swap_checked
#print axioms fusedMap2976swap_checked
#print axioms certified2976swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
