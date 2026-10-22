/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0910 : Family 10 := level10.get ⟨700,by decide⟩
def sourceMap0910 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0910 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0910_checked : acceptsGraphIso
    (source (graph core0910) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2168.graph sourceMap0910=true := by decide +kernel
theorem fusedMap0910_checked : acceptsGraphIso
    (fused (graph core0910) (root 10) 2 2) DegreeTwoThreeSpectrum5441.graph fusedMap0910=true := by decide +kernel
theorem certified0910 : Certified (graph core0910) (root 10) 2 2 :=
  of_native_maps core0910 DegreeOneMiddleResidualSpectrum2168.graph DegreeTwoThreeSpectrum5441.graph
    sourceMap0910 fusedMap0910 sourceMap0910_checked fusedMap0910_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0910
#print axioms sourceMap0910_checked
#print axioms fusedMap0910_checked
#print axioms certified0910
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
