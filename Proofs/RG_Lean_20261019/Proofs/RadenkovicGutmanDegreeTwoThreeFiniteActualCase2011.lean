/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2011 : Family 10 := level10.get ⟨1648,by decide⟩
def sourceMap2011 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap2011 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2011_checked : acceptsGraphIso
    (source (graph core2011) (root 10) 0 2) DegreeTwoThreeSpectrum3799.graph sourceMap2011=true := by decide +kernel
theorem fusedMap2011_checked : acceptsGraphIso
    (fused (graph core2011) (root 10) 0 2) DegreeTwoThreeSpectrum3206.graph fusedMap2011=true := by decide +kernel
theorem certified2011 : Certified (graph core2011) (root 10) 0 2 :=
  of_native_maps core2011 DegreeTwoThreeSpectrum3799.graph DegreeTwoThreeSpectrum3206.graph
    sourceMap2011 fusedMap2011 sourceMap2011_checked fusedMap2011_checked
    DegreeTwoThreeFiniteComparisons.comparison2011
#print axioms sourceMap2011_checked
#print axioms fusedMap2011_checked
#print axioms certified2011
def sourceMap2011swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap2011swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2011swap_checked : acceptsGraphIso
    (source (graph core2011) (root 10) 2 0) DegreeTwoThreeSpectrum3799.graph sourceMap2011swap=true := by decide +kernel
theorem fusedMap2011swap_checked : acceptsGraphIso
    (fused (graph core2011) (root 10) 2 0) DegreeTwoThreeSpectrum3206.graph fusedMap2011swap=true := by decide +kernel
theorem certified2011swap : Certified (graph core2011) (root 10) 2 0 :=
  of_native_maps core2011 DegreeTwoThreeSpectrum3799.graph DegreeTwoThreeSpectrum3206.graph
    sourceMap2011swap fusedMap2011swap sourceMap2011swap_checked fusedMap2011swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2011
#print axioms sourceMap2011swap_checked
#print axioms fusedMap2011swap_checked
#print axioms certified2011swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
