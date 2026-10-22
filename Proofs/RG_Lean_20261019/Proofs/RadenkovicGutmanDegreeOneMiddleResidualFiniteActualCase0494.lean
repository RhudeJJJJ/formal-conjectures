/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0494 : Family 10 := level10.get ⟨11,by decide⟩
def sourceMap0494 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0494 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0494_checked : acceptsGraphIso
    (source (graph core0494) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1171.graph sourceMap0494=true := by decide +kernel
theorem fusedMap0494_checked : acceptsGraphIso
    (fused (graph core0494) (root 10) 2 2) DegreeTwoThreeSpectrum4980.graph fusedMap0494=true := by decide +kernel
theorem certified0494 : Certified (graph core0494) (root 10) 2 2 :=
  of_native_maps core0494 DegreeOneMiddleResidualSpectrum1171.graph DegreeTwoThreeSpectrum4980.graph
    sourceMap0494 fusedMap0494 sourceMap0494_checked fusedMap0494_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0494
#print axioms sourceMap0494_checked
#print axioms fusedMap0494_checked
#print axioms certified0494
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
