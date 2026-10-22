/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2869 : Family 10 := level10.get ⟨1246,by decide⟩
def sourceMap2869 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2869 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2869_checked : acceptsGraphIso
    (source (graph core2869) (root 10) 0 4) DegreeTwoThreeSpectrum6480.graph sourceMap2869=true := by decide +kernel
theorem fusedMap2869_checked : acceptsGraphIso
    (fused (graph core2869) (root 10) 0 4) DegreeTwoThreeSpectrum6481.graph fusedMap2869=true := by decide +kernel
theorem certified2869 : Certified (graph core2869) (root 10) 0 4 :=
  of_native_maps core2869 DegreeTwoThreeSpectrum6480.graph DegreeTwoThreeSpectrum6481.graph
    sourceMap2869 fusedMap2869 sourceMap2869_checked fusedMap2869_checked
    DegreeTwoThreeFiniteComparisons.comparison2869
#print axioms sourceMap2869_checked
#print axioms fusedMap2869_checked
#print axioms certified2869
def sourceMap2869swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2869swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2869swap_checked : acceptsGraphIso
    (source (graph core2869) (root 10) 4 0) DegreeTwoThreeSpectrum6480.graph sourceMap2869swap=true := by decide +kernel
theorem fusedMap2869swap_checked : acceptsGraphIso
    (fused (graph core2869) (root 10) 4 0) DegreeTwoThreeSpectrum6481.graph fusedMap2869swap=true := by decide +kernel
theorem certified2869swap : Certified (graph core2869) (root 10) 4 0 :=
  of_native_maps core2869 DegreeTwoThreeSpectrum6480.graph DegreeTwoThreeSpectrum6481.graph
    sourceMap2869swap fusedMap2869swap sourceMap2869swap_checked fusedMap2869swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2869
#print axioms sourceMap2869swap_checked
#print axioms fusedMap2869swap_checked
#print axioms certified2869swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
