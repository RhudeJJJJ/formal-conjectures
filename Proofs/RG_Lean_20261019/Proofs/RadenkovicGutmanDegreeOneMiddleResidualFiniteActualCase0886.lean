/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0886 : Family 10 := level10.get ⟨641,by decide⟩
def sourceMap0886 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0886 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0886_checked : acceptsGraphIso
    (source (graph core0886) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2129.graph sourceMap0886=true := by decide +kernel
theorem fusedMap0886_checked : acceptsGraphIso
    (fused (graph core0886) (root 10) 2 2) DegreeTwoThreeSpectrum5339.graph fusedMap0886=true := by decide +kernel
theorem certified0886 : Certified (graph core0886) (root 10) 2 2 :=
  of_native_maps core0886 DegreeOneMiddleResidualSpectrum2129.graph DegreeTwoThreeSpectrum5339.graph
    sourceMap0886 fusedMap0886 sourceMap0886_checked fusedMap0886_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0886
#print axioms sourceMap0886_checked
#print axioms fusedMap0886_checked
#print axioms certified0886
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
