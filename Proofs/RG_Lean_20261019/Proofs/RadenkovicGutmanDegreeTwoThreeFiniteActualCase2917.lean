/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2917 : Family 10 := level10.get ⟨1361,by decide⟩
def sourceMap2917 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2917 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2917_checked : acceptsGraphIso
    (source (graph core2917) (root 10) 0 4) DegreeTwoThreeSpectrum6697.graph sourceMap2917=true := by decide +kernel
theorem fusedMap2917_checked : acceptsGraphIso
    (fused (graph core2917) (root 10) 0 4) DegreeTwoThreeSpectrum6698.graph fusedMap2917=true := by decide +kernel
theorem certified2917 : Certified (graph core2917) (root 10) 0 4 :=
  of_native_maps core2917 DegreeTwoThreeSpectrum6697.graph DegreeTwoThreeSpectrum6698.graph
    sourceMap2917 fusedMap2917 sourceMap2917_checked fusedMap2917_checked
    DegreeTwoThreeFiniteComparisons.comparison2917
#print axioms sourceMap2917_checked
#print axioms fusedMap2917_checked
#print axioms certified2917
def sourceMap2917swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2917swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2917swap_checked : acceptsGraphIso
    (source (graph core2917) (root 10) 4 0) DegreeTwoThreeSpectrum6697.graph sourceMap2917swap=true := by decide +kernel
theorem fusedMap2917swap_checked : acceptsGraphIso
    (fused (graph core2917) (root 10) 4 0) DegreeTwoThreeSpectrum6698.graph fusedMap2917swap=true := by decide +kernel
theorem certified2917swap : Certified (graph core2917) (root 10) 4 0 :=
  of_native_maps core2917 DegreeTwoThreeSpectrum6697.graph DegreeTwoThreeSpectrum6698.graph
    sourceMap2917swap fusedMap2917swap sourceMap2917swap_checked fusedMap2917swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2917
#print axioms sourceMap2917swap_checked
#print axioms fusedMap2917swap_checked
#print axioms certified2917swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
