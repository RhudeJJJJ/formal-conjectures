/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2016 : Family 10 := level10.get ⟨1657,by decide⟩
def sourceMap2016 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap2016 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2016_checked : acceptsGraphIso
    (source (graph core2016) (root 10) 0 2) DegreeTwoThreeSpectrum3805.graph sourceMap2016=true := by decide +kernel
theorem fusedMap2016_checked : acceptsGraphIso
    (fused (graph core2016) (root 10) 0 2) DegreeTwoThreeSpectrum3220.graph fusedMap2016=true := by decide +kernel
theorem certified2016 : Certified (graph core2016) (root 10) 0 2 :=
  of_native_maps core2016 DegreeTwoThreeSpectrum3805.graph DegreeTwoThreeSpectrum3220.graph
    sourceMap2016 fusedMap2016 sourceMap2016_checked fusedMap2016_checked
    DegreeTwoThreeFiniteComparisons.comparison2016
#print axioms sourceMap2016_checked
#print axioms fusedMap2016_checked
#print axioms certified2016
def sourceMap2016swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,7,8,9,14] (sourceLabel 10 2 0 v)
def fusedMap2016swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2016swap_checked : acceptsGraphIso
    (source (graph core2016) (root 10) 2 0) DegreeTwoThreeSpectrum3805.graph sourceMap2016swap=true := by decide +kernel
theorem fusedMap2016swap_checked : acceptsGraphIso
    (fused (graph core2016) (root 10) 2 0) DegreeTwoThreeSpectrum3220.graph fusedMap2016swap=true := by decide +kernel
theorem certified2016swap : Certified (graph core2016) (root 10) 2 0 :=
  of_native_maps core2016 DegreeTwoThreeSpectrum3805.graph DegreeTwoThreeSpectrum3220.graph
    sourceMap2016swap fusedMap2016swap sourceMap2016swap_checked fusedMap2016swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2016
#print axioms sourceMap2016swap_checked
#print axioms fusedMap2016swap_checked
#print axioms certified2016swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
