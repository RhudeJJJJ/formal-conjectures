/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0497 : Family 10 := level10.get ⟨14,by decide⟩
def sourceMap0497 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0497 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0497_checked : acceptsGraphIso
    (source (graph core0497) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1228.graph sourceMap0497=true := by decide +kernel
theorem fusedMap0497_checked : acceptsGraphIso
    (fused (graph core0497) (root 10) 2 2) DegreeTwoThreeSpectrum4998.graph fusedMap0497=true := by decide +kernel
theorem certified0497 : Certified (graph core0497) (root 10) 2 2 :=
  of_native_maps core0497 DegreeOneMiddleResidualSpectrum1228.graph DegreeTwoThreeSpectrum4998.graph
    sourceMap0497 fusedMap0497 sourceMap0497_checked fusedMap0497_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0497
#print axioms sourceMap0497_checked
#print axioms fusedMap0497_checked
#print axioms certified0497
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
