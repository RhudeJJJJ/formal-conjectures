/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2017 : Family 10 := level10.get ⟨1662,by decide⟩
def sourceMap2017 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap2017 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2017_checked : acceptsGraphIso
    (source (graph core2017) (root 10) 0 2) DegreeTwoThreeSpectrum3806.graph sourceMap2017=true := by decide +kernel
theorem fusedMap2017_checked : acceptsGraphIso
    (fused (graph core2017) (root 10) 0 2) DegreeTwoThreeSpectrum3235.graph fusedMap2017=true := by decide +kernel
theorem certified2017 : Certified (graph core2017) (root 10) 0 2 :=
  of_native_maps core2017 DegreeTwoThreeSpectrum3806.graph DegreeTwoThreeSpectrum3235.graph
    sourceMap2017 fusedMap2017 sourceMap2017_checked fusedMap2017_checked
    DegreeTwoThreeFiniteComparisons.comparison2017
#print axioms sourceMap2017_checked
#print axioms fusedMap2017_checked
#print axioms certified2017
def sourceMap2017swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap2017swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2017swap_checked : acceptsGraphIso
    (source (graph core2017) (root 10) 2 0) DegreeTwoThreeSpectrum3806.graph sourceMap2017swap=true := by decide +kernel
theorem fusedMap2017swap_checked : acceptsGraphIso
    (fused (graph core2017) (root 10) 2 0) DegreeTwoThreeSpectrum3235.graph fusedMap2017swap=true := by decide +kernel
theorem certified2017swap : Certified (graph core2017) (root 10) 2 0 :=
  of_native_maps core2017 DegreeTwoThreeSpectrum3806.graph DegreeTwoThreeSpectrum3235.graph
    sourceMap2017swap fusedMap2017swap sourceMap2017swap_checked fusedMap2017swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2017
#print axioms sourceMap2017swap_checked
#print axioms fusedMap2017swap_checked
#print axioms certified2017swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
