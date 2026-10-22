/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0993 : Family 10 := level10.get ⟨875,by decide⟩
def sourceMap0993 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0993 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0993_checked : acceptsGraphIso
    (source (graph core0993) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2296.graph sourceMap0993=true := by decide +kernel
theorem fusedMap0993_checked : acceptsGraphIso
    (fused (graph core0993) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1424.graph fusedMap0993=true := by decide +kernel
theorem certified0993 : Certified (graph core0993) (root 10) 2 2 :=
  of_native_maps core0993 DegreeOneMiddleResidualSpectrum2296.graph DegreeOneMiddleResidualSpectrum1424.graph
    sourceMap0993 fusedMap0993 sourceMap0993_checked fusedMap0993_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0993
#print axioms sourceMap0993_checked
#print axioms fusedMap0993_checked
#print axioms certified0993
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
