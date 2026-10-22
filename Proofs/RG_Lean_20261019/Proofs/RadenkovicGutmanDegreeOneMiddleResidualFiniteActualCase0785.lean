/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0785 : Family 10 := level10.get ⟨448,by decide⟩
def sourceMap0785 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0785 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0785_checked : acceptsGraphIso
    (source (graph core0785) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1890.graph sourceMap0785=true := by decide +kernel
theorem fusedMap0785_checked : acceptsGraphIso
    (fused (graph core0785) (root 10) 2 2) DegreeTwoThreeSpectrum5871.graph fusedMap0785=true := by decide +kernel
theorem certified0785 : Certified (graph core0785) (root 10) 2 2 :=
  of_native_maps core0785 DegreeOneMiddleResidualSpectrum1890.graph DegreeTwoThreeSpectrum5871.graph
    sourceMap0785 fusedMap0785 sourceMap0785_checked fusedMap0785_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0785
#print axioms sourceMap0785_checked
#print axioms fusedMap0785_checked
#print axioms certified0785
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
