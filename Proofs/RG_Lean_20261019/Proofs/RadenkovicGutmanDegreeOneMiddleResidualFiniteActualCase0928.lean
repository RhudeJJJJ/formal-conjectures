/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0928 : Family 10 := level10.get ⟨733,by decide⟩
def sourceMap0928 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0928 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0928_checked : acceptsGraphIso
    (source (graph core0928) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2199.graph sourceMap0928=true := by decide +kernel
theorem fusedMap0928_checked : acceptsGraphIso
    (fused (graph core0928) (root 10) 2 2) DegreeTwoThreeSpectrum5490.graph fusedMap0928=true := by decide +kernel
theorem certified0928 : Certified (graph core0928) (root 10) 2 2 :=
  of_native_maps core0928 DegreeOneMiddleResidualSpectrum2199.graph DegreeTwoThreeSpectrum5490.graph
    sourceMap0928 fusedMap0928 sourceMap0928_checked fusedMap0928_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0928
#print axioms sourceMap0928_checked
#print axioms fusedMap0928_checked
#print axioms certified0928
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
