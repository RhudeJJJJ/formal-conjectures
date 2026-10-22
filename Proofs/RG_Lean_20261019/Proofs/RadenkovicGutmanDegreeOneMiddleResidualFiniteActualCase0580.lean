/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0580 : Family 10 := level10.get ⟨122,by decide⟩
def sourceMap0580 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0580 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0580_checked : acceptsGraphIso
    (source (graph core0580) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1906.graph sourceMap0580=true := by decide +kernel
theorem fusedMap0580_checked : acceptsGraphIso
    (fused (graph core0580) (root 10) 2 2) DegreeTwoThreeSpectrum5051.graph fusedMap0580=true := by decide +kernel
theorem certified0580 : Certified (graph core0580) (root 10) 2 2 :=
  of_native_maps core0580 DegreeOneMiddleResidualSpectrum1906.graph DegreeTwoThreeSpectrum5051.graph
    sourceMap0580 fusedMap0580 sourceMap0580_checked fusedMap0580_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0580
#print axioms sourceMap0580_checked
#print axioms fusedMap0580_checked
#print axioms certified0580
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
