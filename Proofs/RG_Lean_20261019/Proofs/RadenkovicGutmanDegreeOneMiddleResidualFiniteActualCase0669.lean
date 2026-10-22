/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0669 : Family 10 := level10.get ⟨254,by decide⟩
def sourceMap0669 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0669 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0669_checked : acceptsGraphIso
    (source (graph core0669) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1682.graph sourceMap0669=true := by decide +kernel
theorem fusedMap0669_checked : acceptsGraphIso
    (fused (graph core0669) (root 10) 2 2) DegreeTwoThreeSpectrum5354.graph fusedMap0669=true := by decide +kernel
theorem certified0669 : Certified (graph core0669) (root 10) 2 2 :=
  of_native_maps core0669 DegreeOneMiddleResidualSpectrum1682.graph DegreeTwoThreeSpectrum5354.graph
    sourceMap0669 fusedMap0669 sourceMap0669_checked fusedMap0669_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0669
#print axioms sourceMap0669_checked
#print axioms fusedMap0669_checked
#print axioms certified0669
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
