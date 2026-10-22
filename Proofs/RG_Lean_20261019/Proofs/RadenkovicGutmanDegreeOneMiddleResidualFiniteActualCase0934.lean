/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0934 : Family 10 := level10.get ⟨743,by decide⟩
def sourceMap0934 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0934 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0934_checked : acceptsGraphIso
    (source (graph core0934) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2212.graph sourceMap0934=true := by decide +kernel
theorem fusedMap0934_checked : acceptsGraphIso
    (fused (graph core0934) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1287.graph fusedMap0934=true := by decide +kernel
theorem certified0934 : Certified (graph core0934) (root 10) 2 2 :=
  of_native_maps core0934 DegreeOneMiddleResidualSpectrum2212.graph DegreeOneMiddleResidualSpectrum1287.graph
    sourceMap0934 fusedMap0934 sourceMap0934_checked fusedMap0934_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0934
#print axioms sourceMap0934_checked
#print axioms fusedMap0934_checked
#print axioms certified0934
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
