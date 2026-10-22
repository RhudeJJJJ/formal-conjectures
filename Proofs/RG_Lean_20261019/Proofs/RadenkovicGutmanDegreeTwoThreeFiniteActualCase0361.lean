/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0361 : Family 9 := level9.get ⟨580,by decide⟩
def sourceMap0361 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0361 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0361_checked : acceptsGraphIso
    (source (graph core0361) (root 9) 0 0) DegreeTwoThreeSpectrum555.graph sourceMap0361=true := by decide +kernel
theorem fusedMap0361_checked : acceptsGraphIso
    (fused (graph core0361) (root 9) 0 0) DegreeTwoThreeSpectrum544.graph fusedMap0361=true := by decide +kernel
theorem certified0361 : Certified (graph core0361) (root 9) 0 0 :=
  of_native_maps core0361 DegreeTwoThreeSpectrum555.graph DegreeTwoThreeSpectrum544.graph
    sourceMap0361 fusedMap0361 sourceMap0361_checked fusedMap0361_checked
    DegreeTwoThreeFiniteComparisons.comparison0361
#print axioms sourceMap0361_checked
#print axioms fusedMap0361_checked
#print axioms certified0361
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
