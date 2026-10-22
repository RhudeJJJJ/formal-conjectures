/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0258 : Family 9 := level9.get ⟨77,by decide⟩
def sourceMap0258 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0258 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0258_checked : acceptsGraphIso
    (source (graph core0258) (root 9) 2 2) DegreeOneMiddleResidualSpectrum666.graph sourceMap0258=true := by decide +kernel
theorem fusedMap0258_checked : acceptsGraphIso
    (fused (graph core0258) (root 9) 2 2) DegreeTwoThreeSpectrum4015.graph fusedMap0258=true := by decide +kernel
theorem certified0258 : Certified (graph core0258) (root 9) 2 2 :=
  of_native_maps core0258 DegreeOneMiddleResidualSpectrum666.graph DegreeTwoThreeSpectrum4015.graph
    sourceMap0258 fusedMap0258 sourceMap0258_checked fusedMap0258_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0258
#print axioms sourceMap0258_checked
#print axioms fusedMap0258_checked
#print axioms certified0258
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
