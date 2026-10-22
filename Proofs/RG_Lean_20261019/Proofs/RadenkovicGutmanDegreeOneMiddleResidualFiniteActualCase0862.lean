/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0862 : Family 10 := level10.get ⟨595,by decide⟩
def sourceMap0862 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0862 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0862_checked : acceptsGraphIso
    (source (graph core0862) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2092.graph sourceMap0862=true := by decide +kernel
theorem fusedMap0862_checked : acceptsGraphIso
    (fused (graph core0862) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1155.graph fusedMap0862=true := by decide +kernel
theorem certified0862 : Certified (graph core0862) (root 10) 2 2 :=
  of_native_maps core0862 DegreeOneMiddleResidualSpectrum2092.graph DegreeOneMiddleResidualSpectrum1155.graph
    sourceMap0862 fusedMap0862 sourceMap0862_checked fusedMap0862_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0862
#print axioms sourceMap0862_checked
#print axioms fusedMap0862_checked
#print axioms certified0862
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
