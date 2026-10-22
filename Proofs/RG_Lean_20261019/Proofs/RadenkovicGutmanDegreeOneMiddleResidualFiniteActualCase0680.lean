/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0680 : Family 10 := level10.get ⟨273,by decide⟩
def sourceMap0680 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,6,0,1,2,3,4,5,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0680 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0680_checked : acceptsGraphIso
    (source (graph core0680) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1699.graph sourceMap0680=true := by decide +kernel
theorem fusedMap0680_checked : acceptsGraphIso
    (fused (graph core0680) (root 10) 2 2) DegreeTwoThreeSpectrum5403.graph fusedMap0680=true := by decide +kernel
theorem certified0680 : Certified (graph core0680) (root 10) 2 2 :=
  of_native_maps core0680 DegreeOneMiddleResidualSpectrum1699.graph DegreeTwoThreeSpectrum5403.graph
    sourceMap0680 fusedMap0680 sourceMap0680_checked fusedMap0680_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0680
#print axioms sourceMap0680_checked
#print axioms fusedMap0680_checked
#print axioms certified0680
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
