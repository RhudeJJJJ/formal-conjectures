/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0818 : Family 10 := level10.get ⟨521,by decide⟩
def sourceMap0818 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0818 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0818_checked : acceptsGraphIso
    (source (graph core0818) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2003.graph sourceMap0818=true := by decide +kernel
theorem fusedMap0818_checked : acceptsGraphIso
    (fused (graph core0818) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1087.graph fusedMap0818=true := by decide +kernel
theorem certified0818 : Certified (graph core0818) (root 10) 2 2 :=
  of_native_maps core0818 DegreeOneMiddleResidualSpectrum2003.graph DegreeOneMiddleResidualSpectrum1087.graph
    sourceMap0818 fusedMap0818 sourceMap0818_checked fusedMap0818_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0818
#print axioms sourceMap0818_checked
#print axioms fusedMap0818_checked
#print axioms certified0818
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
