/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0488 : Family 10 := level10.get ⟨4,by decide⟩
def sourceMap0488 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![3,2,1,0,10,11,12,13,14,15,16,4,5,6,7,8,9] (sourceLabel 10 2 2 v)
def fusedMap0488 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0488_checked : acceptsGraphIso
    (source (graph core0488) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1388.graph sourceMap0488=true := by decide +kernel
theorem fusedMap0488_checked : acceptsGraphIso
    (fused (graph core0488) (root 10) 2 2) DegreeTwoThreeSpectrum4962.graph fusedMap0488=true := by decide +kernel
theorem certified0488 : Certified (graph core0488) (root 10) 2 2 :=
  of_native_maps core0488 DegreeOneMiddleResidualSpectrum1388.graph DegreeTwoThreeSpectrum4962.graph
    sourceMap0488 fusedMap0488 sourceMap0488_checked fusedMap0488_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0488
#print axioms sourceMap0488_checked
#print axioms fusedMap0488_checked
#print axioms certified0488
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
