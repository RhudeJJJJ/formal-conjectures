/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0152 : Family 8 := level8.get ⟨153,by decide⟩
def sourceMap0152 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0152 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0152_checked : acceptsGraphIso
    (source (graph core0152) (root 8) 2 2) DegreeOneMiddleResidualSpectrum319.graph sourceMap0152=true := by decide +kernel
theorem fusedMap0152_checked : acceptsGraphIso
    (fused (graph core0152) (root 8) 2 2) DegreeOneMiddleResidualSpectrum227.graph fusedMap0152=true := by decide +kernel
theorem certified0152 : Certified (graph core0152) (root 8) 2 2 :=
  of_native_maps core0152 DegreeOneMiddleResidualSpectrum319.graph DegreeOneMiddleResidualSpectrum227.graph
    sourceMap0152 fusedMap0152 sourceMap0152_checked fusedMap0152_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0152
#print axioms sourceMap0152_checked
#print axioms fusedMap0152_checked
#print axioms certified0152
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
