/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0635 : Family 10 := level10.get ⟨206,by decide⟩
def sourceMap0635 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0635 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0635_checked : acceptsGraphIso
    (source (graph core0635) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1585.graph sourceMap0635=true := by decide +kernel
theorem fusedMap0635_checked : acceptsGraphIso
    (fused (graph core0635) (root 10) 2 2) DegreeTwoThreeSpectrum5205.graph fusedMap0635=true := by decide +kernel
theorem certified0635 : Certified (graph core0635) (root 10) 2 2 :=
  of_native_maps core0635 DegreeOneMiddleResidualSpectrum1585.graph DegreeTwoThreeSpectrum5205.graph
    sourceMap0635 fusedMap0635 sourceMap0635_checked fusedMap0635_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0635
#print axioms sourceMap0635_checked
#print axioms fusedMap0635_checked
#print axioms certified0635
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
