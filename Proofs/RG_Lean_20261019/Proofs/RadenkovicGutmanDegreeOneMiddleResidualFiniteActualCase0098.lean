/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0098 : Family 8 := level8.get ⟨53,by decide⟩
def sourceMap0098 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0098 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0098_checked : acceptsGraphIso
    (source (graph core0098) (root 8) 2 2) DegreeOneMiddleResidualSpectrum302.graph sourceMap0098=true := by decide +kernel
theorem fusedMap0098_checked : acceptsGraphIso
    (fused (graph core0098) (root 8) 2 2) DegreeTwoThreeSpectrum2349.graph fusedMap0098=true := by decide +kernel
theorem certified0098 : Certified (graph core0098) (root 8) 2 2 :=
  of_native_maps core0098 DegreeOneMiddleResidualSpectrum302.graph DegreeTwoThreeSpectrum2349.graph
    sourceMap0098 fusedMap0098 sourceMap0098_checked fusedMap0098_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0098
#print axioms sourceMap0098_checked
#print axioms fusedMap0098_checked
#print axioms certified0098
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
