/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0575 : Family 10 := level10.get ⟨114,by decide⟩
def sourceMap0575 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0575 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0575_checked : acceptsGraphIso
    (source (graph core0575) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1826.graph sourceMap0575=true := by decide +kernel
theorem fusedMap0575_checked : acceptsGraphIso
    (fused (graph core0575) (root 10) 2 2) DegreeTwoThreeSpectrum5039.graph fusedMap0575=true := by decide +kernel
theorem certified0575 : Certified (graph core0575) (root 10) 2 2 :=
  of_native_maps core0575 DegreeOneMiddleResidualSpectrum1826.graph DegreeTwoThreeSpectrum5039.graph
    sourceMap0575 fusedMap0575 sourceMap0575_checked fusedMap0575_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0575
#print axioms sourceMap0575_checked
#print axioms fusedMap0575_checked
#print axioms certified0575
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
