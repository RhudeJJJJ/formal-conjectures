/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2464 : Family 10 := level10.get ⟨66,by decide⟩
def sourceMap2464 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2464 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2464_checked : acceptsGraphIso
    (source (graph core2464) (root 10) 0 4) DegreeTwoThreeSpectrum5302.graph sourceMap2464=true := by decide +kernel
theorem fusedMap2464_checked : acceptsGraphIso
    (fused (graph core2464) (root 10) 0 4) DegreeTwoThreeSpectrum4979.graph fusedMap2464=true := by decide +kernel
theorem certified2464 : Certified (graph core2464) (root 10) 0 4 :=
  of_native_maps core2464 DegreeTwoThreeSpectrum5302.graph DegreeTwoThreeSpectrum4979.graph
    sourceMap2464 fusedMap2464 sourceMap2464_checked fusedMap2464_checked
    DegreeTwoThreeFiniteComparisons.comparison2464
#print axioms sourceMap2464_checked
#print axioms fusedMap2464_checked
#print axioms certified2464
def sourceMap2464swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2464swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2464swap_checked : acceptsGraphIso
    (source (graph core2464) (root 10) 4 0) DegreeTwoThreeSpectrum5302.graph sourceMap2464swap=true := by decide +kernel
theorem fusedMap2464swap_checked : acceptsGraphIso
    (fused (graph core2464) (root 10) 4 0) DegreeTwoThreeSpectrum4979.graph fusedMap2464swap=true := by decide +kernel
theorem certified2464swap : Certified (graph core2464) (root 10) 4 0 :=
  of_native_maps core2464 DegreeTwoThreeSpectrum5302.graph DegreeTwoThreeSpectrum4979.graph
    sourceMap2464swap fusedMap2464swap sourceMap2464swap_checked fusedMap2464swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2464
#print axioms sourceMap2464swap_checked
#print axioms fusedMap2464swap_checked
#print axioms certified2464swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
