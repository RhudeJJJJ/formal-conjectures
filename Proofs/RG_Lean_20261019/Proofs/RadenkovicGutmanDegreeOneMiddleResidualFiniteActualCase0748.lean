/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0748 : Family 10 := level10.get ⟨383,by decide⟩
def sourceMap0748 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0748 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0748_checked : acceptsGraphIso
    (source (graph core0748) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1877.graph sourceMap0748=true := by decide +kernel
theorem fusedMap0748_checked : acceptsGraphIso
    (fused (graph core0748) (root 10) 2 2) DegreeTwoThreeSpectrum5712.graph fusedMap0748=true := by decide +kernel
theorem certified0748 : Certified (graph core0748) (root 10) 2 2 :=
  of_native_maps core0748 DegreeOneMiddleResidualSpectrum1877.graph DegreeTwoThreeSpectrum5712.graph
    sourceMap0748 fusedMap0748 sourceMap0748_checked fusedMap0748_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0748
#print axioms sourceMap0748_checked
#print axioms fusedMap0748_checked
#print axioms certified0748
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
