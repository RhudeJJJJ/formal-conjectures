/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0329 : Family 9 := level9.get ⟨191,by decide⟩
def sourceMap0329 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap0329 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0329_checked : acceptsGraphIso
    (source (graph core0329) (root 9) 2 2) DegreeOneMiddleResidualSpectrum815.graph sourceMap0329=true := by decide +kernel
theorem fusedMap0329_checked : acceptsGraphIso
    (fused (graph core0329) (root 9) 2 2) DegreeOneMiddleResidualSpectrum443.graph fusedMap0329=true := by decide +kernel
theorem certified0329 : Certified (graph core0329) (root 9) 2 2 :=
  of_native_maps core0329 DegreeOneMiddleResidualSpectrum815.graph DegreeOneMiddleResidualSpectrum443.graph
    sourceMap0329 fusedMap0329 sourceMap0329_checked fusedMap0329_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0329
#print axioms sourceMap0329_checked
#print axioms fusedMap0329_checked
#print axioms certified0329
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
