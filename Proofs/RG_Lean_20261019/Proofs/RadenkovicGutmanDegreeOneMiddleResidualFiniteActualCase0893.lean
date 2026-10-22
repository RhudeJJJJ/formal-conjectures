/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0893 : Family 10 := level10.get ⟨656,by decide⟩
def sourceMap0893 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap0893 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0893_checked : acceptsGraphIso
    (source (graph core0893) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2136.graph sourceMap0893=true := by decide +kernel
theorem fusedMap0893_checked : acceptsGraphIso
    (fused (graph core0893) (root 10) 2 2) DegreeTwoThreeSpectrum5365.graph fusedMap0893=true := by decide +kernel
theorem certified0893 : Certified (graph core0893) (root 10) 2 2 :=
  of_native_maps core0893 DegreeOneMiddleResidualSpectrum2136.graph DegreeTwoThreeSpectrum5365.graph
    sourceMap0893 fusedMap0893 sourceMap0893_checked fusedMap0893_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0893
#print axioms sourceMap0893_checked
#print axioms fusedMap0893_checked
#print axioms certified0893
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
