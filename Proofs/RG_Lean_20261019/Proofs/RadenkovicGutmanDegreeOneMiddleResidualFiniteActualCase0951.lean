/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0951 : Family 10 := level10.get ⟨775,by decide⟩
def sourceMap0951 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0951 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0951_checked : acceptsGraphIso
    (source (graph core0951) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2238.graph sourceMap0951=true := by decide +kernel
theorem fusedMap0951_checked : acceptsGraphIso
    (fused (graph core0951) (root 10) 2 2) DegreeTwoThreeSpectrum5553.graph fusedMap0951=true := by decide +kernel
theorem certified0951 : Certified (graph core0951) (root 10) 2 2 :=
  of_native_maps core0951 DegreeOneMiddleResidualSpectrum2238.graph DegreeTwoThreeSpectrum5553.graph
    sourceMap0951 fusedMap0951 sourceMap0951_checked fusedMap0951_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0951
#print axioms sourceMap0951_checked
#print axioms fusedMap0951_checked
#print axioms certified0951
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
