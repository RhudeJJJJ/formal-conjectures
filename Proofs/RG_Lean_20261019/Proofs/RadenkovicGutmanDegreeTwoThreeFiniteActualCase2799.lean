/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2799 : Family 10 := level10.get ⟨1075,by decide⟩
def sourceMap2799 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2799 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2799_checked : acceptsGraphIso
    (source (graph core2799) (root 10) 0 4) DegreeTwoThreeSpectrum6134.graph sourceMap2799=true := by decide +kernel
theorem fusedMap2799_checked : acceptsGraphIso
    (fused (graph core2799) (root 10) 0 4) DegreeTwoThreeSpectrum6135.graph fusedMap2799=true := by decide +kernel
theorem certified2799 : Certified (graph core2799) (root 10) 0 4 :=
  of_native_maps core2799 DegreeTwoThreeSpectrum6134.graph DegreeTwoThreeSpectrum6135.graph
    sourceMap2799 fusedMap2799 sourceMap2799_checked fusedMap2799_checked
    DegreeTwoThreeFiniteComparisons.comparison2799
#print axioms sourceMap2799_checked
#print axioms fusedMap2799_checked
#print axioms certified2799
def sourceMap2799swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2799swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2799swap_checked : acceptsGraphIso
    (source (graph core2799) (root 10) 4 0) DegreeTwoThreeSpectrum6134.graph sourceMap2799swap=true := by decide +kernel
theorem fusedMap2799swap_checked : acceptsGraphIso
    (fused (graph core2799) (root 10) 4 0) DegreeTwoThreeSpectrum6135.graph fusedMap2799swap=true := by decide +kernel
theorem certified2799swap : Certified (graph core2799) (root 10) 4 0 :=
  of_native_maps core2799 DegreeTwoThreeSpectrum6134.graph DegreeTwoThreeSpectrum6135.graph
    sourceMap2799swap fusedMap2799swap sourceMap2799swap_checked fusedMap2799swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2799
#print axioms sourceMap2799swap_checked
#print axioms fusedMap2799swap_checked
#print axioms certified2799swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
