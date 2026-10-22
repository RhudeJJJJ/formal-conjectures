/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0510 : Family 10 := level10.get ⟨29,by decide⟩
def sourceMap0510 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0510 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0510_checked : acceptsGraphIso
    (source (graph core0510) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1383.graph sourceMap0510=true := by decide +kernel
theorem fusedMap0510_checked : acceptsGraphIso
    (fused (graph core0510) (root 10) 2 2) DegreeTwoThreeSpectrum5071.graph fusedMap0510=true := by decide +kernel
theorem certified0510 : Certified (graph core0510) (root 10) 2 2 :=
  of_native_maps core0510 DegreeOneMiddleResidualSpectrum1383.graph DegreeTwoThreeSpectrum5071.graph
    sourceMap0510 fusedMap0510 sourceMap0510_checked fusedMap0510_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0510
#print axioms sourceMap0510_checked
#print axioms fusedMap0510_checked
#print axioms certified0510
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
