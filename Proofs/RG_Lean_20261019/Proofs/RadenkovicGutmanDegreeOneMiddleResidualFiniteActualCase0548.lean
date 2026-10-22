/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0548 : Family 10 := level10.get ⟨78,by decide⟩
def sourceMap0548 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0548 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0548_checked : acceptsGraphIso
    (source (graph core0548) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1705.graph sourceMap0548=true := by decide +kernel
theorem fusedMap0548_checked : acceptsGraphIso
    (fused (graph core0548) (root 10) 2 2) DegreeTwoThreeSpectrum4994.graph fusedMap0548=true := by decide +kernel
theorem certified0548 : Certified (graph core0548) (root 10) 2 2 :=
  of_native_maps core0548 DegreeOneMiddleResidualSpectrum1705.graph DegreeTwoThreeSpectrum4994.graph
    sourceMap0548 fusedMap0548 sourceMap0548_checked fusedMap0548_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0548
#print axioms sourceMap0548_checked
#print axioms fusedMap0548_checked
#print axioms certified0548
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
