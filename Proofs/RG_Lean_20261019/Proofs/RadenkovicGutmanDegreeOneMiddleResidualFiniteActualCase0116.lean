/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0116 : Family 8 := level8.get ⟨79,by decide⟩
def sourceMap0116 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap0116 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0116_checked : acceptsGraphIso
    (source (graph core0116) (root 8) 2 2) DegreeOneMiddleResidualSpectrum337.graph sourceMap0116=true := by decide +kernel
theorem fusedMap0116_checked : acceptsGraphIso
    (fused (graph core0116) (root 8) 2 2) DegreeTwoThreeSpectrum2395.graph fusedMap0116=true := by decide +kernel
theorem certified0116 : Certified (graph core0116) (root 8) 2 2 :=
  of_native_maps core0116 DegreeOneMiddleResidualSpectrum337.graph DegreeTwoThreeSpectrum2395.graph
    sourceMap0116 fusedMap0116 sourceMap0116_checked fusedMap0116_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0116
#print axioms sourceMap0116_checked
#print axioms fusedMap0116_checked
#print axioms certified0116
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
