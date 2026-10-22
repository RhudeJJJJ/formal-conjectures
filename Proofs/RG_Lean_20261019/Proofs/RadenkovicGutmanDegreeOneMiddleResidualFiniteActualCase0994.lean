/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0994 : Family 10 := level10.get ⟨876,by decide⟩
def sourceMap0994 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0994 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0994_checked : acceptsGraphIso
    (source (graph core0994) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2297.graph sourceMap0994=true := by decide +kernel
theorem fusedMap0994_checked : acceptsGraphIso
    (fused (graph core0994) (root 10) 2 2) DegreeTwoThreeSpectrum5726.graph fusedMap0994=true := by decide +kernel
theorem certified0994 : Certified (graph core0994) (root 10) 2 2 :=
  of_native_maps core0994 DegreeOneMiddleResidualSpectrum2297.graph DegreeTwoThreeSpectrum5726.graph
    sourceMap0994 fusedMap0994 sourceMap0994_checked fusedMap0994_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0994
#print axioms sourceMap0994_checked
#print axioms fusedMap0994_checked
#print axioms certified0994
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
