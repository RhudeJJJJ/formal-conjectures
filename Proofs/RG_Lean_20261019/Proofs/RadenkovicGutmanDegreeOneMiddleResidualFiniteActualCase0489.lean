/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0489 : Family 10 := level10.get ⟨5,by decide⟩
def sourceMap0489 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![3,2,1,0,10,11,12,13,14,15,16,4,5,6,7,8,9] (sourceLabel 10 2 2 v)
def fusedMap0489 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0489_checked : acceptsGraphIso
    (source (graph core0489) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1391.graph sourceMap0489=true := by decide +kernel
theorem fusedMap0489_checked : acceptsGraphIso
    (fused (graph core0489) (root 10) 2 2) DegreeTwoThreeSpectrum4963.graph fusedMap0489=true := by decide +kernel
theorem certified0489 : Certified (graph core0489) (root 10) 2 2 :=
  of_native_maps core0489 DegreeOneMiddleResidualSpectrum1391.graph DegreeTwoThreeSpectrum4963.graph
    sourceMap0489 fusedMap0489 sourceMap0489_checked fusedMap0489_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0489
#print axioms sourceMap0489_checked
#print axioms fusedMap0489_checked
#print axioms certified0489
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
