/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0365 : Family 9 := level9.get ⟨259,by decide⟩
def sourceMap0365 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0365 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0365_checked : acceptsGraphIso
    (source (graph core0365) (root 9) 2 2) DegreeOneMiddleResidualSpectrum884.graph sourceMap0365=true := by decide +kernel
theorem fusedMap0365_checked : acceptsGraphIso
    (fused (graph core0365) (root 9) 2 2) DegreeOneMiddleResidualSpectrum508.graph fusedMap0365=true := by decide +kernel
theorem certified0365 : Certified (graph core0365) (root 9) 2 2 :=
  of_native_maps core0365 DegreeOneMiddleResidualSpectrum884.graph DegreeOneMiddleResidualSpectrum508.graph
    sourceMap0365 fusedMap0365 sourceMap0365_checked fusedMap0365_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0365
#print axioms sourceMap0365_checked
#print axioms fusedMap0365_checked
#print axioms certified0365
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
