/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0943 : Family 10 := level10.get ⟨1561,by decide⟩
def sourceMap0943 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0943 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0943_checked : acceptsGraphIso
    (source (graph core0943) (root 10) 0 0) DegreeTwoThreeSpectrum1338.graph sourceMap0943=true := by decide +kernel
theorem fusedMap0943_checked : acceptsGraphIso
    (fused (graph core0943) (root 10) 0 0) DegreeTwoThreeSpectrum1337.graph fusedMap0943=true := by decide +kernel
theorem certified0943 : Certified (graph core0943) (root 10) 0 0 :=
  of_native_maps core0943 DegreeTwoThreeSpectrum1338.graph DegreeTwoThreeSpectrum1337.graph
    sourceMap0943 fusedMap0943 sourceMap0943_checked fusedMap0943_checked
    DegreeTwoThreeFiniteComparisons.comparison0943
#print axioms sourceMap0943_checked
#print axioms fusedMap0943_checked
#print axioms certified0943
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
