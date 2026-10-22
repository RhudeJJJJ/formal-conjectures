/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2923 : Family 10 := level10.get ⟨1372,by decide⟩
def sourceMap2923 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2923 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2923_checked : acceptsGraphIso
    (source (graph core2923) (root 10) 0 4) DegreeTwoThreeSpectrum6715.graph sourceMap2923=true := by decide +kernel
theorem fusedMap2923_checked : acceptsGraphIso
    (fused (graph core2923) (root 10) 0 4) DegreeTwoThreeSpectrum6716.graph fusedMap2923=true := by decide +kernel
theorem certified2923 : Certified (graph core2923) (root 10) 0 4 :=
  of_native_maps core2923 DegreeTwoThreeSpectrum6715.graph DegreeTwoThreeSpectrum6716.graph
    sourceMap2923 fusedMap2923 sourceMap2923_checked fusedMap2923_checked
    DegreeTwoThreeFiniteComparisons.comparison2923
#print axioms sourceMap2923_checked
#print axioms fusedMap2923_checked
#print axioms certified2923
def sourceMap2923swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2923swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2923swap_checked : acceptsGraphIso
    (source (graph core2923) (root 10) 4 0) DegreeTwoThreeSpectrum6715.graph sourceMap2923swap=true := by decide +kernel
theorem fusedMap2923swap_checked : acceptsGraphIso
    (fused (graph core2923) (root 10) 4 0) DegreeTwoThreeSpectrum6716.graph fusedMap2923swap=true := by decide +kernel
theorem certified2923swap : Certified (graph core2923) (root 10) 4 0 :=
  of_native_maps core2923 DegreeTwoThreeSpectrum6715.graph DegreeTwoThreeSpectrum6716.graph
    sourceMap2923swap fusedMap2923swap sourceMap2923swap_checked fusedMap2923swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2923
#print axioms sourceMap2923swap_checked
#print axioms fusedMap2923swap_checked
#print axioms certified2923swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
