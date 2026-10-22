/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2013 : Family 10 := level10.get ⟨1651,by decide⟩
def sourceMap2013 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap2013 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2013_checked : acceptsGraphIso
    (source (graph core2013) (root 10) 0 2) DegreeTwoThreeSpectrum3801.graph sourceMap2013=true := by decide +kernel
theorem fusedMap2013_checked : acceptsGraphIso
    (fused (graph core2013) (root 10) 0 2) DegreeTwoThreeSpectrum3210.graph fusedMap2013=true := by decide +kernel
theorem certified2013 : Certified (graph core2013) (root 10) 0 2 :=
  of_native_maps core2013 DegreeTwoThreeSpectrum3801.graph DegreeTwoThreeSpectrum3210.graph
    sourceMap2013 fusedMap2013 sourceMap2013_checked fusedMap2013_checked
    DegreeTwoThreeFiniteComparisons.comparison2013
#print axioms sourceMap2013_checked
#print axioms fusedMap2013_checked
#print axioms certified2013
def sourceMap2013swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap2013swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2013swap_checked : acceptsGraphIso
    (source (graph core2013) (root 10) 2 0) DegreeTwoThreeSpectrum3801.graph sourceMap2013swap=true := by decide +kernel
theorem fusedMap2013swap_checked : acceptsGraphIso
    (fused (graph core2013) (root 10) 2 0) DegreeTwoThreeSpectrum3210.graph fusedMap2013swap=true := by decide +kernel
theorem certified2013swap : Certified (graph core2013) (root 10) 2 0 :=
  of_native_maps core2013 DegreeTwoThreeSpectrum3801.graph DegreeTwoThreeSpectrum3210.graph
    sourceMap2013swap fusedMap2013swap sourceMap2013swap_checked fusedMap2013swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2013
#print axioms sourceMap2013swap_checked
#print axioms fusedMap2013swap_checked
#print axioms certified2013swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
