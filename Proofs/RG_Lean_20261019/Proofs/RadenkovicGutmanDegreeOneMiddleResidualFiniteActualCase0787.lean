/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0787 : Family 10 := level10.get ⟨451,by decide⟩
def sourceMap0787 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0787 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0787_checked : acceptsGraphIso
    (source (graph core0787) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1871.graph sourceMap0787=true := by decide +kernel
theorem fusedMap0787_checked : acceptsGraphIso
    (fused (graph core0787) (root 10) 2 2) DegreeTwoThreeSpectrum5878.graph fusedMap0787=true := by decide +kernel
theorem certified0787 : Certified (graph core0787) (root 10) 2 2 :=
  of_native_maps core0787 DegreeOneMiddleResidualSpectrum1871.graph DegreeTwoThreeSpectrum5878.graph
    sourceMap0787 fusedMap0787 sourceMap0787_checked fusedMap0787_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0787
#print axioms sourceMap0787_checked
#print axioms fusedMap0787_checked
#print axioms certified0787
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
