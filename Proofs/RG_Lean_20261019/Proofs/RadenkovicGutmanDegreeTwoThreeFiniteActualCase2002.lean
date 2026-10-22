/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2002 : Family 10 := level10.get ⟨1628,by decide⟩
def sourceMap2002 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap2002 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2002_checked : acceptsGraphIso
    (source (graph core2002) (root 10) 0 2) DegreeTwoThreeSpectrum3789.graph sourceMap2002=true := by decide +kernel
theorem fusedMap2002_checked : acceptsGraphIso
    (fused (graph core2002) (root 10) 0 2) DegreeTwoThreeSpectrum3172.graph fusedMap2002=true := by decide +kernel
theorem certified2002 : Certified (graph core2002) (root 10) 0 2 :=
  of_native_maps core2002 DegreeTwoThreeSpectrum3789.graph DegreeTwoThreeSpectrum3172.graph
    sourceMap2002 fusedMap2002 sourceMap2002_checked fusedMap2002_checked
    DegreeTwoThreeFiniteComparisons.comparison2002
#print axioms sourceMap2002_checked
#print axioms fusedMap2002_checked
#print axioms certified2002
def sourceMap2002swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap2002swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2002swap_checked : acceptsGraphIso
    (source (graph core2002) (root 10) 2 0) DegreeTwoThreeSpectrum3789.graph sourceMap2002swap=true := by decide +kernel
theorem fusedMap2002swap_checked : acceptsGraphIso
    (fused (graph core2002) (root 10) 2 0) DegreeTwoThreeSpectrum3172.graph fusedMap2002swap=true := by decide +kernel
theorem certified2002swap : Certified (graph core2002) (root 10) 2 0 :=
  of_native_maps core2002 DegreeTwoThreeSpectrum3789.graph DegreeTwoThreeSpectrum3172.graph
    sourceMap2002swap fusedMap2002swap sourceMap2002swap_checked fusedMap2002swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2002
#print axioms sourceMap2002swap_checked
#print axioms fusedMap2002swap_checked
#print axioms certified2002swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
