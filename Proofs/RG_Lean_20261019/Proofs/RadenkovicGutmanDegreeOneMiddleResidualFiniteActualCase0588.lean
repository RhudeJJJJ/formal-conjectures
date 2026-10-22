/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0588 : Family 10 := level10.get ⟨132,by decide⟩
def sourceMap0588 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0588 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0588_checked : acceptsGraphIso
    (source (graph core0588) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1920.graph sourceMap0588=true := by decide +kernel
theorem fusedMap0588_checked : acceptsGraphIso
    (fused (graph core0588) (root 10) 2 2) DegreeTwoThreeSpectrum5062.graph fusedMap0588=true := by decide +kernel
theorem certified0588 : Certified (graph core0588) (root 10) 2 2 :=
  of_native_maps core0588 DegreeOneMiddleResidualSpectrum1920.graph DegreeTwoThreeSpectrum5062.graph
    sourceMap0588 fusedMap0588 sourceMap0588_checked fusedMap0588_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0588
#print axioms sourceMap0588_checked
#print axioms fusedMap0588_checked
#print axioms certified0588
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
