/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2034 : Family 10 := level10.get ⟨1719,by decide⟩
def sourceMap2034 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap2034 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2034_checked : acceptsGraphIso
    (source (graph core2034) (root 10) 0 2) DegreeTwoThreeSpectrum3829.graph sourceMap2034=true := by decide +kernel
theorem fusedMap2034_checked : acceptsGraphIso
    (fused (graph core2034) (root 10) 0 2) DegreeTwoThreeSpectrum3403.graph fusedMap2034=true := by decide +kernel
theorem certified2034 : Certified (graph core2034) (root 10) 0 2 :=
  of_native_maps core2034 DegreeTwoThreeSpectrum3829.graph DegreeTwoThreeSpectrum3403.graph
    sourceMap2034 fusedMap2034 sourceMap2034_checked fusedMap2034_checked
    DegreeTwoThreeFiniteComparisons.comparison2034
#print axioms sourceMap2034_checked
#print axioms fusedMap2034_checked
#print axioms certified2034
def sourceMap2034swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,7,8,9,14] (sourceLabel 10 2 0 v)
def fusedMap2034swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2034swap_checked : acceptsGraphIso
    (source (graph core2034) (root 10) 2 0) DegreeTwoThreeSpectrum3829.graph sourceMap2034swap=true := by decide +kernel
theorem fusedMap2034swap_checked : acceptsGraphIso
    (fused (graph core2034) (root 10) 2 0) DegreeTwoThreeSpectrum3403.graph fusedMap2034swap=true := by decide +kernel
theorem certified2034swap : Certified (graph core2034) (root 10) 2 0 :=
  of_native_maps core2034 DegreeTwoThreeSpectrum3829.graph DegreeTwoThreeSpectrum3403.graph
    sourceMap2034swap fusedMap2034swap sourceMap2034swap_checked fusedMap2034swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2034
#print axioms sourceMap2034swap_checked
#print axioms fusedMap2034swap_checked
#print axioms certified2034swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
