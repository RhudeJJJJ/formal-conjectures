/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2929 : Family 10 := level10.get ⟨1382,by decide⟩
def sourceMap2929 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2929 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2929_checked : acceptsGraphIso
    (source (graph core2929) (root 10) 0 4) DegreeTwoThreeSpectrum6735.graph sourceMap2929=true := by decide +kernel
theorem fusedMap2929_checked : acceptsGraphIso
    (fused (graph core2929) (root 10) 0 4) DegreeTwoThreeSpectrum6736.graph fusedMap2929=true := by decide +kernel
theorem certified2929 : Certified (graph core2929) (root 10) 0 4 :=
  of_native_maps core2929 DegreeTwoThreeSpectrum6735.graph DegreeTwoThreeSpectrum6736.graph
    sourceMap2929 fusedMap2929 sourceMap2929_checked fusedMap2929_checked
    DegreeTwoThreeFiniteComparisons.comparison2929
#print axioms sourceMap2929_checked
#print axioms fusedMap2929_checked
#print axioms certified2929
def sourceMap2929swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2929swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2929swap_checked : acceptsGraphIso
    (source (graph core2929) (root 10) 4 0) DegreeTwoThreeSpectrum6735.graph sourceMap2929swap=true := by decide +kernel
theorem fusedMap2929swap_checked : acceptsGraphIso
    (fused (graph core2929) (root 10) 4 0) DegreeTwoThreeSpectrum6736.graph fusedMap2929swap=true := by decide +kernel
theorem certified2929swap : Certified (graph core2929) (root 10) 4 0 :=
  of_native_maps core2929 DegreeTwoThreeSpectrum6735.graph DegreeTwoThreeSpectrum6736.graph
    sourceMap2929swap fusedMap2929swap sourceMap2929swap_checked fusedMap2929swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2929
#print axioms sourceMap2929swap_checked
#print axioms fusedMap2929swap_checked
#print axioms certified2929swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
