/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0094 : Family 8 := level8.get ⟨45,by decide⟩
def sourceMap0094 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0094 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0094_checked : acceptsGraphIso
    (source (graph core0094) (root 8) 2 2) DegreeOneMiddleResidualSpectrum294.graph sourceMap0094=true := by decide +kernel
theorem fusedMap0094_checked : acceptsGraphIso
    (fused (graph core0094) (root 8) 2 2) DegreeTwoThreeSpectrum2329.graph fusedMap0094=true := by decide +kernel
theorem certified0094 : Certified (graph core0094) (root 8) 2 2 :=
  of_native_maps core0094 DegreeOneMiddleResidualSpectrum294.graph DegreeTwoThreeSpectrum2329.graph
    sourceMap0094 fusedMap0094 sourceMap0094_checked fusedMap0094_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0094
#print axioms sourceMap0094_checked
#print axioms fusedMap0094_checked
#print axioms certified0094
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
