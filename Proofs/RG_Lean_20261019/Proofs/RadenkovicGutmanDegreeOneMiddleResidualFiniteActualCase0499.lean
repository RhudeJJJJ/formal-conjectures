/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0499 : Family 10 := level10.get ⟨16,by decide⟩
def sourceMap0499 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0499 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap0499_checked : acceptsGraphIso
    (source (graph core0499) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1229.graph sourceMap0499=true := by decide +kernel
theorem fusedMap0499_checked : acceptsGraphIso
    (fused (graph core0499) (root 10) 2 2) DegreeTwoThreeSpectrum5007.graph fusedMap0499=true := by decide +kernel
theorem certified0499 : Certified (graph core0499) (root 10) 2 2 :=
  of_native_maps core0499 DegreeOneMiddleResidualSpectrum1229.graph DegreeTwoThreeSpectrum5007.graph
    sourceMap0499 fusedMap0499 sourceMap0499_checked fusedMap0499_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0499
#print axioms sourceMap0499_checked
#print axioms fusedMap0499_checked
#print axioms certified0499
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
