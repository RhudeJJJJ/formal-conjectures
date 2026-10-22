/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0666 : Family 10 := level10.get ⟨250,by decide⟩
def sourceMap0666 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0666 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0666_checked : acceptsGraphIso
    (source (graph core0666) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1678.graph sourceMap0666=true := by decide +kernel
theorem fusedMap0666_checked : acceptsGraphIso
    (fused (graph core0666) (root 10) 2 2) DegreeTwoThreeSpectrum5343.graph fusedMap0666=true := by decide +kernel
theorem certified0666 : Certified (graph core0666) (root 10) 2 2 :=
  of_native_maps core0666 DegreeOneMiddleResidualSpectrum1678.graph DegreeTwoThreeSpectrum5343.graph
    sourceMap0666 fusedMap0666 sourceMap0666_checked fusedMap0666_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0666
#print axioms sourceMap0666_checked
#print axioms fusedMap0666_checked
#print axioms certified0666
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
