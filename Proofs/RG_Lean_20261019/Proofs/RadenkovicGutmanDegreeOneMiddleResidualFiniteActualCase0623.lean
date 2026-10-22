/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0623 : Family 10 := level10.get ⟨191,by decide⟩
def sourceMap0623 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0623 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0623_checked : acceptsGraphIso
    (source (graph core0623) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1540.graph sourceMap0623=true := by decide +kernel
theorem fusedMap0623_checked : acceptsGraphIso
    (fused (graph core0623) (root 10) 2 2) DegreeTwoThreeSpectrum5149.graph fusedMap0623=true := by decide +kernel
theorem certified0623 : Certified (graph core0623) (root 10) 2 2 :=
  of_native_maps core0623 DegreeOneMiddleResidualSpectrum1540.graph DegreeTwoThreeSpectrum5149.graph
    sourceMap0623 fusedMap0623 sourceMap0623_checked fusedMap0623_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0623
#print axioms sourceMap0623_checked
#print axioms fusedMap0623_checked
#print axioms certified0623
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
