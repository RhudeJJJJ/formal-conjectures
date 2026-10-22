/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0361 : Family 9 := level9.get ⟨254,by decide⟩
def sourceMap0361 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0361 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0361_checked : acceptsGraphIso
    (source (graph core0361) (root 9) 2 2) DegreeOneMiddleResidualSpectrum876.graph sourceMap0361=true := by decide +kernel
theorem fusedMap0361_checked : acceptsGraphIso
    (fused (graph core0361) (root 9) 2 2) DegreeTwoThreeSpectrum4063.graph fusedMap0361=true := by decide +kernel
theorem certified0361 : Certified (graph core0361) (root 9) 2 2 :=
  of_native_maps core0361 DegreeOneMiddleResidualSpectrum876.graph DegreeTwoThreeSpectrum4063.graph
    sourceMap0361 fusedMap0361 sourceMap0361_checked fusedMap0361_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0361
#print axioms sourceMap0361_checked
#print axioms fusedMap0361_checked
#print axioms certified0361
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
