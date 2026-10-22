/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0799 : Family 10 := level10.get ⟨476,by decide⟩
def sourceMap0799 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,8,9,10,11,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0799 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0799_checked : acceptsGraphIso
    (source (graph core0799) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1850.graph sourceMap0799=true := by decide +kernel
theorem fusedMap0799_checked : acceptsGraphIso
    (fused (graph core0799) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1505.graph fusedMap0799=true := by decide +kernel
theorem certified0799 : Certified (graph core0799) (root 10) 2 2 :=
  of_native_maps core0799 DegreeOneMiddleResidualSpectrum1850.graph DegreeOneMiddleResidualSpectrum1505.graph
    sourceMap0799 fusedMap0799 sourceMap0799_checked fusedMap0799_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0799
#print axioms sourceMap0799_checked
#print axioms fusedMap0799_checked
#print axioms certified0799
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
