/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2005 : Family 10 := level10.get ⟨1634,by decide⟩
def sourceMap2005 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap2005 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2005_checked : acceptsGraphIso
    (source (graph core2005) (root 10) 0 2) DegreeTwoThreeSpectrum3792.graph sourceMap2005=true := by decide +kernel
theorem fusedMap2005_checked : acceptsGraphIso
    (fused (graph core2005) (root 10) 0 2) DegreeTwoThreeSpectrum3179.graph fusedMap2005=true := by decide +kernel
theorem certified2005 : Certified (graph core2005) (root 10) 0 2 :=
  of_native_maps core2005 DegreeTwoThreeSpectrum3792.graph DegreeTwoThreeSpectrum3179.graph
    sourceMap2005 fusedMap2005 sourceMap2005_checked fusedMap2005_checked
    DegreeTwoThreeFiniteComparisons.comparison2005
#print axioms sourceMap2005_checked
#print axioms fusedMap2005_checked
#print axioms certified2005
def sourceMap2005swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap2005swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2005swap_checked : acceptsGraphIso
    (source (graph core2005) (root 10) 2 0) DegreeTwoThreeSpectrum3792.graph sourceMap2005swap=true := by decide +kernel
theorem fusedMap2005swap_checked : acceptsGraphIso
    (fused (graph core2005) (root 10) 2 0) DegreeTwoThreeSpectrum3179.graph fusedMap2005swap=true := by decide +kernel
theorem certified2005swap : Certified (graph core2005) (root 10) 2 0 :=
  of_native_maps core2005 DegreeTwoThreeSpectrum3792.graph DegreeTwoThreeSpectrum3179.graph
    sourceMap2005swap fusedMap2005swap sourceMap2005swap_checked fusedMap2005swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2005
#print axioms sourceMap2005swap_checked
#print axioms fusedMap2005swap_checked
#print axioms certified2005swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
