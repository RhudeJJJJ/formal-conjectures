/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0552 : Family 10 := level10.get ⟨83,by decide⟩
def sourceMap0552 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0552 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0552_checked : acceptsGraphIso
    (source (graph core0552) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1703.graph sourceMap0552=true := by decide +kernel
theorem fusedMap0552_checked : acceptsGraphIso
    (fused (graph core0552) (root 10) 2 2) DegreeTwoThreeSpectrum5000.graph fusedMap0552=true := by decide +kernel
theorem certified0552 : Certified (graph core0552) (root 10) 2 2 :=
  of_native_maps core0552 DegreeOneMiddleResidualSpectrum1703.graph DegreeTwoThreeSpectrum5000.graph
    sourceMap0552 fusedMap0552 sourceMap0552_checked fusedMap0552_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0552
#print axioms sourceMap0552_checked
#print axioms fusedMap0552_checked
#print axioms certified0552
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
