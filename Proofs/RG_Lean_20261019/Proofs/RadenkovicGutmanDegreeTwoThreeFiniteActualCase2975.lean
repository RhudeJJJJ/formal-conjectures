/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2975 : Family 10 := level10.get ⟨1495,by decide⟩
def sourceMap2975 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2975 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2975_checked : acceptsGraphIso
    (source (graph core2975) (root 10) 0 4) DegreeTwoThreeSpectrum6997.graph sourceMap2975=true := by decide +kernel
theorem fusedMap2975_checked : acceptsGraphIso
    (fused (graph core2975) (root 10) 0 4) DegreeTwoThreeSpectrum6998.graph fusedMap2975=true := by decide +kernel
theorem certified2975 : Certified (graph core2975) (root 10) 0 4 :=
  of_native_maps core2975 DegreeTwoThreeSpectrum6997.graph DegreeTwoThreeSpectrum6998.graph
    sourceMap2975 fusedMap2975 sourceMap2975_checked fusedMap2975_checked
    DegreeTwoThreeFiniteComparisons.comparison2975
#print axioms sourceMap2975_checked
#print axioms fusedMap2975_checked
#print axioms certified2975
def sourceMap2975swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2975swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2975swap_checked : acceptsGraphIso
    (source (graph core2975) (root 10) 4 0) DegreeTwoThreeSpectrum6997.graph sourceMap2975swap=true := by decide +kernel
theorem fusedMap2975swap_checked : acceptsGraphIso
    (fused (graph core2975) (root 10) 4 0) DegreeTwoThreeSpectrum6998.graph fusedMap2975swap=true := by decide +kernel
theorem certified2975swap : Certified (graph core2975) (root 10) 4 0 :=
  of_native_maps core2975 DegreeTwoThreeSpectrum6997.graph DegreeTwoThreeSpectrum6998.graph
    sourceMap2975swap fusedMap2975swap sourceMap2975swap_checked fusedMap2975swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2975
#print axioms sourceMap2975swap_checked
#print axioms fusedMap2975swap_checked
#print axioms certified2975swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
