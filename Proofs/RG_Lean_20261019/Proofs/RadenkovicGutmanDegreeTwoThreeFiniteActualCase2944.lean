/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2944 : Family 10 := level10.get ⟨1423,by decide⟩
def sourceMap2944 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2944 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2944_checked : acceptsGraphIso
    (source (graph core2944) (root 10) 0 4) DegreeTwoThreeSpectrum6876.graph sourceMap2944=true := by decide +kernel
theorem fusedMap2944_checked : acceptsGraphIso
    (fused (graph core2944) (root 10) 0 4) DegreeTwoThreeSpectrum6877.graph fusedMap2944=true := by decide +kernel
theorem certified2944 : Certified (graph core2944) (root 10) 0 4 :=
  of_native_maps core2944 DegreeTwoThreeSpectrum6876.graph DegreeTwoThreeSpectrum6877.graph
    sourceMap2944 fusedMap2944 sourceMap2944_checked fusedMap2944_checked
    DegreeTwoThreeFiniteComparisons.comparison2944
#print axioms sourceMap2944_checked
#print axioms fusedMap2944_checked
#print axioms certified2944
def sourceMap2944swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2944swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2944swap_checked : acceptsGraphIso
    (source (graph core2944) (root 10) 4 0) DegreeTwoThreeSpectrum6876.graph sourceMap2944swap=true := by decide +kernel
theorem fusedMap2944swap_checked : acceptsGraphIso
    (fused (graph core2944) (root 10) 4 0) DegreeTwoThreeSpectrum6877.graph fusedMap2944swap=true := by decide +kernel
theorem certified2944swap : Certified (graph core2944) (root 10) 4 0 :=
  of_native_maps core2944 DegreeTwoThreeSpectrum6876.graph DegreeTwoThreeSpectrum6877.graph
    sourceMap2944swap fusedMap2944swap sourceMap2944swap_checked fusedMap2944swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2944
#print axioms sourceMap2944swap_checked
#print axioms fusedMap2944swap_checked
#print axioms certified2944swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
