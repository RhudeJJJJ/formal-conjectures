/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0841 : Family 10 := level10.get ⟨563,by decide⟩
def sourceMap0841 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0841 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0841_checked : acceptsGraphIso
    (source (graph core0841) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2047.graph sourceMap0841=true := by decide +kernel
theorem fusedMap0841_checked : acceptsGraphIso
    (fused (graph core0841) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1125.graph fusedMap0841=true := by decide +kernel
theorem certified0841 : Certified (graph core0841) (root 10) 2 2 :=
  of_native_maps core0841 DegreeOneMiddleResidualSpectrum2047.graph DegreeOneMiddleResidualSpectrum1125.graph
    sourceMap0841 fusedMap0841 sourceMap0841_checked fusedMap0841_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0841
#print axioms sourceMap0841_checked
#print axioms fusedMap0841_checked
#print axioms certified0841
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
