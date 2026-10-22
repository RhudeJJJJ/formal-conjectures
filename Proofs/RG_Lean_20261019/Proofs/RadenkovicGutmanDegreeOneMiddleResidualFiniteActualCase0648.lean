/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0648 : Family 10 := level10.get ⟨224,by decide⟩
def sourceMap0648 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0648 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0648_checked : acceptsGraphIso
    (source (graph core0648) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1632.graph sourceMap0648=true := by decide +kernel
theorem fusedMap0648_checked : acceptsGraphIso
    (fused (graph core0648) (root 10) 2 2) DegreeTwoThreeSpectrum5261.graph fusedMap0648=true := by decide +kernel
theorem certified0648 : Certified (graph core0648) (root 10) 2 2 :=
  of_native_maps core0648 DegreeOneMiddleResidualSpectrum1632.graph DegreeTwoThreeSpectrum5261.graph
    sourceMap0648 fusedMap0648 sourceMap0648_checked fusedMap0648_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0648
#print axioms sourceMap0648_checked
#print axioms fusedMap0648_checked
#print axioms certified0648
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
