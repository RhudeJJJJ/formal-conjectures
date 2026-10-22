/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2845 : Family 10 := level10.get ⟨1191,by decide⟩
def sourceMap2845 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2845 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2845_checked : acceptsGraphIso
    (source (graph core2845) (root 10) 0 4) DegreeTwoThreeSpectrum6362.graph sourceMap2845=true := by decide +kernel
theorem fusedMap2845_checked : acceptsGraphIso
    (fused (graph core2845) (root 10) 0 4) DegreeTwoThreeSpectrum6363.graph fusedMap2845=true := by decide +kernel
theorem certified2845 : Certified (graph core2845) (root 10) 0 4 :=
  of_native_maps core2845 DegreeTwoThreeSpectrum6362.graph DegreeTwoThreeSpectrum6363.graph
    sourceMap2845 fusedMap2845 sourceMap2845_checked fusedMap2845_checked
    DegreeTwoThreeFiniteComparisons.comparison2845
#print axioms sourceMap2845_checked
#print axioms fusedMap2845_checked
#print axioms certified2845
def sourceMap2845swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2845swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2845swap_checked : acceptsGraphIso
    (source (graph core2845) (root 10) 4 0) DegreeTwoThreeSpectrum6362.graph sourceMap2845swap=true := by decide +kernel
theorem fusedMap2845swap_checked : acceptsGraphIso
    (fused (graph core2845) (root 10) 4 0) DegreeTwoThreeSpectrum6363.graph fusedMap2845swap=true := by decide +kernel
theorem certified2845swap : Certified (graph core2845) (root 10) 4 0 :=
  of_native_maps core2845 DegreeTwoThreeSpectrum6362.graph DegreeTwoThreeSpectrum6363.graph
    sourceMap2845swap fusedMap2845swap sourceMap2845swap_checked fusedMap2845swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2845
#print axioms sourceMap2845swap_checked
#print axioms fusedMap2845swap_checked
#print axioms certified2845swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
