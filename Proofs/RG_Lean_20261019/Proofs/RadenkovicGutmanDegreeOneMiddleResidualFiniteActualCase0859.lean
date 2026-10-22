/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0859 : Family 10 := level10.get ⟨591,by decide⟩
def sourceMap0859 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0859 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0859_checked : acceptsGraphIso
    (source (graph core0859) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2086.graph sourceMap0859=true := by decide +kernel
theorem fusedMap0859_checked : acceptsGraphIso
    (fused (graph core0859) (root 10) 2 2) DegreeTwoThreeSpectrum5265.graph fusedMap0859=true := by decide +kernel
theorem certified0859 : Certified (graph core0859) (root 10) 2 2 :=
  of_native_maps core0859 DegreeOneMiddleResidualSpectrum2086.graph DegreeTwoThreeSpectrum5265.graph
    sourceMap0859 fusedMap0859 sourceMap0859_checked fusedMap0859_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0859
#print axioms sourceMap0859_checked
#print axioms fusedMap0859_checked
#print axioms certified0859
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
