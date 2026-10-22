/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0937 : Family 10 := level10.get ⟨747,by decide⟩
def sourceMap0937 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0937 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0937_checked : acceptsGraphIso
    (source (graph core0937) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2215.graph sourceMap0937=true := by decide +kernel
theorem fusedMap0937_checked : acceptsGraphIso
    (fused (graph core0937) (root 10) 2 2) DegreeTwoThreeSpectrum5509.graph fusedMap0937=true := by decide +kernel
theorem certified0937 : Certified (graph core0937) (root 10) 2 2 :=
  of_native_maps core0937 DegreeOneMiddleResidualSpectrum2215.graph DegreeTwoThreeSpectrum5509.graph
    sourceMap0937 fusedMap0937 sourceMap0937_checked fusedMap0937_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0937
#print axioms sourceMap0937_checked
#print axioms fusedMap0937_checked
#print axioms certified0937
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
