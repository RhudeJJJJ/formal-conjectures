/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2800 : Family 10 := level10.get ⟨1078,by decide⟩
def sourceMap2800 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2800 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2800_checked : acceptsGraphIso
    (source (graph core2800) (root 10) 0 4) DegreeTwoThreeSpectrum6138.graph sourceMap2800=true := by decide +kernel
theorem fusedMap2800_checked : acceptsGraphIso
    (fused (graph core2800) (root 10) 0 4) DegreeTwoThreeSpectrum6139.graph fusedMap2800=true := by decide +kernel
theorem certified2800 : Certified (graph core2800) (root 10) 0 4 :=
  of_native_maps core2800 DegreeTwoThreeSpectrum6138.graph DegreeTwoThreeSpectrum6139.graph
    sourceMap2800 fusedMap2800 sourceMap2800_checked fusedMap2800_checked
    DegreeTwoThreeFiniteComparisons.comparison2800
#print axioms sourceMap2800_checked
#print axioms fusedMap2800_checked
#print axioms certified2800
def sourceMap2800swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2800swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2800swap_checked : acceptsGraphIso
    (source (graph core2800) (root 10) 4 0) DegreeTwoThreeSpectrum6138.graph sourceMap2800swap=true := by decide +kernel
theorem fusedMap2800swap_checked : acceptsGraphIso
    (fused (graph core2800) (root 10) 4 0) DegreeTwoThreeSpectrum6139.graph fusedMap2800swap=true := by decide +kernel
theorem certified2800swap : Certified (graph core2800) (root 10) 4 0 :=
  of_native_maps core2800 DegreeTwoThreeSpectrum6138.graph DegreeTwoThreeSpectrum6139.graph
    sourceMap2800swap fusedMap2800swap sourceMap2800swap_checked fusedMap2800swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2800
#print axioms sourceMap2800swap_checked
#print axioms fusedMap2800swap_checked
#print axioms certified2800swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
