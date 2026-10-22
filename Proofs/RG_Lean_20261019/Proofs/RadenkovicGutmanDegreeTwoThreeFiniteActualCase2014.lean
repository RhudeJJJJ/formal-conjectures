/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2014 : Family 10 := level10.get ⟨1654,by decide⟩
def sourceMap2014 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap2014 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2014_checked : acceptsGraphIso
    (source (graph core2014) (root 10) 0 2) DegreeTwoThreeSpectrum3802.graph sourceMap2014=true := by decide +kernel
theorem fusedMap2014_checked : acceptsGraphIso
    (fused (graph core2014) (root 10) 0 2) DegreeTwoThreeSpectrum3217.graph fusedMap2014=true := by decide +kernel
theorem certified2014 : Certified (graph core2014) (root 10) 0 2 :=
  of_native_maps core2014 DegreeTwoThreeSpectrum3802.graph DegreeTwoThreeSpectrum3217.graph
    sourceMap2014 fusedMap2014 sourceMap2014_checked fusedMap2014_checked
    DegreeTwoThreeFiniteComparisons.comparison2014
#print axioms sourceMap2014_checked
#print axioms fusedMap2014_checked
#print axioms certified2014
def sourceMap2014swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap2014swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2014swap_checked : acceptsGraphIso
    (source (graph core2014) (root 10) 2 0) DegreeTwoThreeSpectrum3802.graph sourceMap2014swap=true := by decide +kernel
theorem fusedMap2014swap_checked : acceptsGraphIso
    (fused (graph core2014) (root 10) 2 0) DegreeTwoThreeSpectrum3217.graph fusedMap2014swap=true := by decide +kernel
theorem certified2014swap : Certified (graph core2014) (root 10) 2 0 :=
  of_native_maps core2014 DegreeTwoThreeSpectrum3802.graph DegreeTwoThreeSpectrum3217.graph
    sourceMap2014swap fusedMap2014swap sourceMap2014swap_checked fusedMap2014swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2014
#print axioms sourceMap2014swap_checked
#print axioms fusedMap2014swap_checked
#print axioms certified2014swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
