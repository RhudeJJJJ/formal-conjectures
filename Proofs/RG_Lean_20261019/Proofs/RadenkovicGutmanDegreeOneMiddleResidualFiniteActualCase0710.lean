/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0710 : Family 10 := level10.get ⟨323,by decide⟩
def sourceMap0710 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0710 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0710_checked : acceptsGraphIso
    (source (graph core0710) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1786.graph sourceMap0710=true := by decide +kernel
theorem fusedMap0710_checked : acceptsGraphIso
    (fused (graph core0710) (root 10) 2 2) DegreeTwoThreeSpectrum5544.graph fusedMap0710=true := by decide +kernel
theorem certified0710 : Certified (graph core0710) (root 10) 2 2 :=
  of_native_maps core0710 DegreeOneMiddleResidualSpectrum1786.graph DegreeTwoThreeSpectrum5544.graph
    sourceMap0710 fusedMap0710 sourceMap0710_checked fusedMap0710_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0710
#print axioms sourceMap0710_checked
#print axioms fusedMap0710_checked
#print axioms certified0710
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
