/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0869 : Family 10 := level10.get ⟨607,by decide⟩
def sourceMap0869 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0869 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0869_checked : acceptsGraphIso
    (source (graph core0869) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2099.graph sourceMap0869=true := by decide +kernel
theorem fusedMap0869_checked : acceptsGraphIso
    (fused (graph core0869) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1166.graph fusedMap0869=true := by decide +kernel
theorem certified0869 : Certified (graph core0869) (root 10) 2 2 :=
  of_native_maps core0869 DegreeOneMiddleResidualSpectrum2099.graph DegreeOneMiddleResidualSpectrum1166.graph
    sourceMap0869 fusedMap0869 sourceMap0869_checked fusedMap0869_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0869
#print axioms sourceMap0869_checked
#print axioms fusedMap0869_checked
#print axioms certified0869
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
