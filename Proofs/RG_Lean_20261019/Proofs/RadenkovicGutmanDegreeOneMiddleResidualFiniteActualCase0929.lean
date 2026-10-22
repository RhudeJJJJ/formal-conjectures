/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0929 : Family 10 := level10.get ⟨734,by decide⟩
def sourceMap0929 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0929 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0929_checked : acceptsGraphIso
    (source (graph core0929) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2200.graph sourceMap0929=true := by decide +kernel
theorem fusedMap0929_checked : acceptsGraphIso
    (fused (graph core0929) (root 10) 2 2) DegreeTwoThreeSpectrum5491.graph fusedMap0929=true := by decide +kernel
theorem certified0929 : Certified (graph core0929) (root 10) 2 2 :=
  of_native_maps core0929 DegreeOneMiddleResidualSpectrum2200.graph DegreeTwoThreeSpectrum5491.graph
    sourceMap0929 fusedMap0929 sourceMap0929_checked fusedMap0929_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0929
#print axioms sourceMap0929_checked
#print axioms fusedMap0929_checked
#print axioms certified0929
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
