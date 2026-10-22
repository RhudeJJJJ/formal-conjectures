/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0763 : Family 10 := level10.get ⟨408,by decide⟩
def sourceMap0763 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0763 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0763_checked : acceptsGraphIso
    (source (graph core0763) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1919.graph sourceMap0763=true := by decide +kernel
theorem fusedMap0763_checked : acceptsGraphIso
    (fused (graph core0763) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1453.graph fusedMap0763=true := by decide +kernel
theorem certified0763 : Certified (graph core0763) (root 10) 2 2 :=
  of_native_maps core0763 DegreeOneMiddleResidualSpectrum1919.graph DegreeOneMiddleResidualSpectrum1453.graph
    sourceMap0763 fusedMap0763 sourceMap0763_checked fusedMap0763_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0763
#print axioms sourceMap0763_checked
#print axioms fusedMap0763_checked
#print axioms certified0763
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
