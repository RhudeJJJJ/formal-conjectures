/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2610 : Family 10 := level10.get ⟨562,by decide⟩
def sourceMap2610 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2610 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2610_checked : acceptsGraphIso
    (source (graph core2610) (root 10) 0 4) DegreeTwoThreeSpectrum6189.graph sourceMap2610=true := by decide +kernel
theorem fusedMap2610_checked : acceptsGraphIso
    (fused (graph core2610) (root 10) 0 4) DegreeTwoThreeSpectrum5227.graph fusedMap2610=true := by decide +kernel
theorem certified2610 : Certified (graph core2610) (root 10) 0 4 :=
  of_native_maps core2610 DegreeTwoThreeSpectrum6189.graph DegreeTwoThreeSpectrum5227.graph
    sourceMap2610 fusedMap2610 sourceMap2610_checked fusedMap2610_checked
    DegreeTwoThreeFiniteComparisons.comparison2610
#print axioms sourceMap2610_checked
#print axioms fusedMap2610_checked
#print axioms certified2610
def sourceMap2610swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2610swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2610swap_checked : acceptsGraphIso
    (source (graph core2610) (root 10) 4 0) DegreeTwoThreeSpectrum6189.graph sourceMap2610swap=true := by decide +kernel
theorem fusedMap2610swap_checked : acceptsGraphIso
    (fused (graph core2610) (root 10) 4 0) DegreeTwoThreeSpectrum5227.graph fusedMap2610swap=true := by decide +kernel
theorem certified2610swap : Certified (graph core2610) (root 10) 4 0 :=
  of_native_maps core2610 DegreeTwoThreeSpectrum6189.graph DegreeTwoThreeSpectrum5227.graph
    sourceMap2610swap fusedMap2610swap sourceMap2610swap_checked fusedMap2610swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2610
#print axioms sourceMap2610swap_checked
#print axioms fusedMap2610swap_checked
#print axioms certified2610swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
