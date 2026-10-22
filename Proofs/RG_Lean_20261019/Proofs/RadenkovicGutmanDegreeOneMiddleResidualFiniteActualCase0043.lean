/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0043 : Family 7 := level7.get ⟨73,by decide⟩
def sourceMap0043 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0043 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0043_checked : acceptsGraphIso
    (source (graph core0043) (root 7) 2 2) DegreeOneMiddleResidualSpectrum100.graph sourceMap0043=true := by decide +kernel
theorem fusedMap0043_checked : acceptsGraphIso
    (fused (graph core0043) (root 7) 2 2) DegreeOneMiddleResidualSpectrum029.graph fusedMap0043=true := by decide +kernel
theorem certified0043 : Certified (graph core0043) (root 7) 2 2 :=
  of_native_maps core0043 DegreeOneMiddleResidualSpectrum100.graph DegreeOneMiddleResidualSpectrum029.graph
    sourceMap0043 fusedMap0043 sourceMap0043_checked fusedMap0043_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0043
#print axioms sourceMap0043_checked
#print axioms fusedMap0043_checked
#print axioms certified0043
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
