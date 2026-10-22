/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2963 : Family 10 := level10.get ⟨1463,by decide⟩
def sourceMap2963 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2963 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2963_checked : acceptsGraphIso
    (source (graph core2963) (root 10) 0 4) DegreeTwoThreeSpectrum6939.graph sourceMap2963=true := by decide +kernel
theorem fusedMap2963_checked : acceptsGraphIso
    (fused (graph core2963) (root 10) 0 4) DegreeTwoThreeSpectrum6940.graph fusedMap2963=true := by decide +kernel
theorem certified2963 : Certified (graph core2963) (root 10) 0 4 :=
  of_native_maps core2963 DegreeTwoThreeSpectrum6939.graph DegreeTwoThreeSpectrum6940.graph
    sourceMap2963 fusedMap2963 sourceMap2963_checked fusedMap2963_checked
    DegreeTwoThreeFiniteComparisons.comparison2963
#print axioms sourceMap2963_checked
#print axioms fusedMap2963_checked
#print axioms certified2963
def sourceMap2963swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2963swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2963swap_checked : acceptsGraphIso
    (source (graph core2963) (root 10) 4 0) DegreeTwoThreeSpectrum6939.graph sourceMap2963swap=true := by decide +kernel
theorem fusedMap2963swap_checked : acceptsGraphIso
    (fused (graph core2963) (root 10) 4 0) DegreeTwoThreeSpectrum6940.graph fusedMap2963swap=true := by decide +kernel
theorem certified2963swap : Certified (graph core2963) (root 10) 4 0 :=
  of_native_maps core2963 DegreeTwoThreeSpectrum6939.graph DegreeTwoThreeSpectrum6940.graph
    sourceMap2963swap fusedMap2963swap sourceMap2963swap_checked fusedMap2963swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2963
#print axioms sourceMap2963swap_checked
#print axioms fusedMap2963swap_checked
#print axioms certified2963swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
