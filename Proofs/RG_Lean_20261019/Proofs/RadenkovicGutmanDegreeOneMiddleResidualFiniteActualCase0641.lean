/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0641 : Family 10 := level10.get ⟨216,by decide⟩
def sourceMap0641 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0641 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0641_checked : acceptsGraphIso
    (source (graph core0641) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1611.graph sourceMap0641=true := by decide +kernel
theorem fusedMap0641_checked : acceptsGraphIso
    (fused (graph core0641) (root 10) 2 2) DegreeTwoThreeSpectrum5232.graph fusedMap0641=true := by decide +kernel
theorem certified0641 : Certified (graph core0641) (root 10) 2 2 :=
  of_native_maps core0641 DegreeOneMiddleResidualSpectrum1611.graph DegreeTwoThreeSpectrum5232.graph
    sourceMap0641 fusedMap0641 sourceMap0641_checked fusedMap0641_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0641
#print axioms sourceMap0641_checked
#print axioms fusedMap0641_checked
#print axioms certified0641
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
