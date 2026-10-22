/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0632 : Family 10 := level10.get ⟨202,by decide⟩
def sourceMap0632 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0632 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0632_checked : acceptsGraphIso
    (source (graph core0632) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1581.graph sourceMap0632=true := by decide +kernel
theorem fusedMap0632_checked : acceptsGraphIso
    (fused (graph core0632) (root 10) 2 2) DegreeTwoThreeSpectrum5191.graph fusedMap0632=true := by decide +kernel
theorem certified0632 : Certified (graph core0632) (root 10) 2 2 :=
  of_native_maps core0632 DegreeOneMiddleResidualSpectrum1581.graph DegreeTwoThreeSpectrum5191.graph
    sourceMap0632 fusedMap0632 sourceMap0632_checked fusedMap0632_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0632
#print axioms sourceMap0632_checked
#print axioms fusedMap0632_checked
#print axioms certified0632
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
