/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2007 : Family 10 := level10.get ⟨1638,by decide⟩
def sourceMap2007 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap2007 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2007_checked : acceptsGraphIso
    (source (graph core2007) (root 10) 0 2) DegreeTwoThreeSpectrum3794.graph sourceMap2007=true := by decide +kernel
theorem fusedMap2007_checked : acceptsGraphIso
    (fused (graph core2007) (root 10) 0 2) DegreeTwoThreeSpectrum3187.graph fusedMap2007=true := by decide +kernel
theorem certified2007 : Certified (graph core2007) (root 10) 0 2 :=
  of_native_maps core2007 DegreeTwoThreeSpectrum3794.graph DegreeTwoThreeSpectrum3187.graph
    sourceMap2007 fusedMap2007 sourceMap2007_checked fusedMap2007_checked
    DegreeTwoThreeFiniteComparisons.comparison2007
#print axioms sourceMap2007_checked
#print axioms fusedMap2007_checked
#print axioms certified2007
def sourceMap2007swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap2007swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2007swap_checked : acceptsGraphIso
    (source (graph core2007) (root 10) 2 0) DegreeTwoThreeSpectrum3794.graph sourceMap2007swap=true := by decide +kernel
theorem fusedMap2007swap_checked : acceptsGraphIso
    (fused (graph core2007) (root 10) 2 0) DegreeTwoThreeSpectrum3187.graph fusedMap2007swap=true := by decide +kernel
theorem certified2007swap : Certified (graph core2007) (root 10) 2 0 :=
  of_native_maps core2007 DegreeTwoThreeSpectrum3794.graph DegreeTwoThreeSpectrum3187.graph
    sourceMap2007swap fusedMap2007swap sourceMap2007swap_checked fusedMap2007swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2007
#print axioms sourceMap2007swap_checked
#print axioms fusedMap2007swap_checked
#print axioms certified2007swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
