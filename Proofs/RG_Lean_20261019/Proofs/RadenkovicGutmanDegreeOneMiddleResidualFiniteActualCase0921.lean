/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0921 : Family 10 := level10.get ⟨717,by decide⟩
def sourceMap0921 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0921 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0921_checked : acceptsGraphIso
    (source (graph core0921) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2184.graph sourceMap0921=true := by decide +kernel
theorem fusedMap0921_checked : acceptsGraphIso
    (fused (graph core0921) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1264.graph fusedMap0921=true := by decide +kernel
theorem certified0921 : Certified (graph core0921) (root 10) 2 2 :=
  of_native_maps core0921 DegreeOneMiddleResidualSpectrum2184.graph DegreeOneMiddleResidualSpectrum1264.graph
    sourceMap0921 fusedMap0921 sourceMap0921_checked fusedMap0921_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0921
#print axioms sourceMap0921_checked
#print axioms fusedMap0921_checked
#print axioms certified0921
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
