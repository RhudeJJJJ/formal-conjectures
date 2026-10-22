/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0606 : Family 10 := level10.get ⟨157,by decide⟩
def sourceMap0606 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0606 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0606_checked : acceptsGraphIso
    (source (graph core0606) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1892.graph sourceMap0606=true := by decide +kernel
theorem fusedMap0606_checked : acceptsGraphIso
    (fused (graph core0606) (root 10) 2 2) DegreeTwoThreeSpectrum5094.graph fusedMap0606=true := by decide +kernel
theorem certified0606 : Certified (graph core0606) (root 10) 2 2 :=
  of_native_maps core0606 DegreeOneMiddleResidualSpectrum1892.graph DegreeTwoThreeSpectrum5094.graph
    sourceMap0606 fusedMap0606 sourceMap0606_checked fusedMap0606_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0606
#print axioms sourceMap0606_checked
#print axioms fusedMap0606_checked
#print axioms certified0606
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
