/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2001 : Family 10 := level10.get ⟨1627,by decide⟩
def sourceMap2001 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap2001 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2001_checked : acceptsGraphIso
    (source (graph core2001) (root 10) 0 2) DegreeTwoThreeSpectrum3788.graph sourceMap2001=true := by decide +kernel
theorem fusedMap2001_checked : acceptsGraphIso
    (fused (graph core2001) (root 10) 0 2) DegreeTwoThreeSpectrum3171.graph fusedMap2001=true := by decide +kernel
theorem certified2001 : Certified (graph core2001) (root 10) 0 2 :=
  of_native_maps core2001 DegreeTwoThreeSpectrum3788.graph DegreeTwoThreeSpectrum3171.graph
    sourceMap2001 fusedMap2001 sourceMap2001_checked fusedMap2001_checked
    DegreeTwoThreeFiniteComparisons.comparison2001
#print axioms sourceMap2001_checked
#print axioms fusedMap2001_checked
#print axioms certified2001
def sourceMap2001swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap2001swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2001swap_checked : acceptsGraphIso
    (source (graph core2001) (root 10) 2 0) DegreeTwoThreeSpectrum3788.graph sourceMap2001swap=true := by decide +kernel
theorem fusedMap2001swap_checked : acceptsGraphIso
    (fused (graph core2001) (root 10) 2 0) DegreeTwoThreeSpectrum3171.graph fusedMap2001swap=true := by decide +kernel
theorem certified2001swap : Certified (graph core2001) (root 10) 2 0 :=
  of_native_maps core2001 DegreeTwoThreeSpectrum3788.graph DegreeTwoThreeSpectrum3171.graph
    sourceMap2001swap fusedMap2001swap sourceMap2001swap_checked fusedMap2001swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2001
#print axioms sourceMap2001swap_checked
#print axioms fusedMap2001swap_checked
#print axioms certified2001swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
