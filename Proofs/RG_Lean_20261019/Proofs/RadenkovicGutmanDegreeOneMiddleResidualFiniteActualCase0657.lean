/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0657 : Family 10 := level10.get ⟨236,by decide⟩
def sourceMap0657 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0657 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0657_checked : acceptsGraphIso
    (source (graph core0657) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1652.graph sourceMap0657=true := by decide +kernel
theorem fusedMap0657_checked : acceptsGraphIso
    (fused (graph core0657) (root 10) 2 2) DegreeTwoThreeSpectrum5298.graph fusedMap0657=true := by decide +kernel
theorem certified0657 : Certified (graph core0657) (root 10) 2 2 :=
  of_native_maps core0657 DegreeOneMiddleResidualSpectrum1652.graph DegreeTwoThreeSpectrum5298.graph
    sourceMap0657 fusedMap0657 sourceMap0657_checked fusedMap0657_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0657
#print axioms sourceMap0657_checked
#print axioms fusedMap0657_checked
#print axioms certified0657
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
