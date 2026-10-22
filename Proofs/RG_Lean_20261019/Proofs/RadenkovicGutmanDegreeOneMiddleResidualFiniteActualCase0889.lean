/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0889 : Family 10 := level10.get ⟨645,by decide⟩
def sourceMap0889 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0889 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0889_checked : acceptsGraphIso
    (source (graph core0889) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2132.graph sourceMap0889=true := by decide +kernel
theorem fusedMap0889_checked : acceptsGraphIso
    (fused (graph core0889) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1200.graph fusedMap0889=true := by decide +kernel
theorem certified0889 : Certified (graph core0889) (root 10) 2 2 :=
  of_native_maps core0889 DegreeOneMiddleResidualSpectrum2132.graph DegreeOneMiddleResidualSpectrum1200.graph
    sourceMap0889 fusedMap0889 sourceMap0889_checked fusedMap0889_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0889
#print axioms sourceMap0889_checked
#print axioms fusedMap0889_checked
#print axioms certified0889
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
