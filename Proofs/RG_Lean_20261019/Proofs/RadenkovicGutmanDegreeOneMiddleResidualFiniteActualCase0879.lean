/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0879 : Family 10 := level10.get ⟨626,by decide⟩
def sourceMap0879 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0879 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0879_checked : acceptsGraphIso
    (source (graph core0879) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2121.graph sourceMap0879=true := by decide +kernel
theorem fusedMap0879_checked : acceptsGraphIso
    (fused (graph core0879) (root 10) 2 2) DegreeTwoThreeSpectrum5316.graph fusedMap0879=true := by decide +kernel
theorem certified0879 : Certified (graph core0879) (root 10) 2 2 :=
  of_native_maps core0879 DegreeOneMiddleResidualSpectrum2121.graph DegreeTwoThreeSpectrum5316.graph
    sourceMap0879 fusedMap0879 sourceMap0879_checked fusedMap0879_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0879
#print axioms sourceMap0879_checked
#print axioms fusedMap0879_checked
#print axioms certified0879
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
