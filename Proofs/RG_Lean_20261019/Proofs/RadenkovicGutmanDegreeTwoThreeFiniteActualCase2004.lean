/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2004 : Family 10 := level10.get ⟨1632,by decide⟩
def sourceMap2004 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap2004 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2004_checked : acceptsGraphIso
    (source (graph core2004) (root 10) 0 2) DegreeTwoThreeSpectrum3791.graph sourceMap2004=true := by decide +kernel
theorem fusedMap2004_checked : acceptsGraphIso
    (fused (graph core2004) (root 10) 0 2) DegreeTwoThreeSpectrum3176.graph fusedMap2004=true := by decide +kernel
theorem certified2004 : Certified (graph core2004) (root 10) 0 2 :=
  of_native_maps core2004 DegreeTwoThreeSpectrum3791.graph DegreeTwoThreeSpectrum3176.graph
    sourceMap2004 fusedMap2004 sourceMap2004_checked fusedMap2004_checked
    DegreeTwoThreeFiniteComparisons.comparison2004
#print axioms sourceMap2004_checked
#print axioms fusedMap2004_checked
#print axioms certified2004
def sourceMap2004swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap2004swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2004swap_checked : acceptsGraphIso
    (source (graph core2004) (root 10) 2 0) DegreeTwoThreeSpectrum3791.graph sourceMap2004swap=true := by decide +kernel
theorem fusedMap2004swap_checked : acceptsGraphIso
    (fused (graph core2004) (root 10) 2 0) DegreeTwoThreeSpectrum3176.graph fusedMap2004swap=true := by decide +kernel
theorem certified2004swap : Certified (graph core2004) (root 10) 2 0 :=
  of_native_maps core2004 DegreeTwoThreeSpectrum3791.graph DegreeTwoThreeSpectrum3176.graph
    sourceMap2004swap fusedMap2004swap sourceMap2004swap_checked fusedMap2004swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2004
#print axioms sourceMap2004swap_checked
#print axioms fusedMap2004swap_checked
#print axioms certified2004swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
