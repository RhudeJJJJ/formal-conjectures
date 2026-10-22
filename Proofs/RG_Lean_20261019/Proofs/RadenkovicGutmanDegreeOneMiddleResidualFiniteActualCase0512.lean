/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0512 : Family 10 := level10.get ⟨31,by decide⟩
def sourceMap0512 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0512 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap0512_checked : acceptsGraphIso
    (source (graph core0512) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1370.graph sourceMap0512=true := by decide +kernel
theorem fusedMap0512_checked : acceptsGraphIso
    (fused (graph core0512) (root 10) 2 2) DegreeTwoThreeSpectrum5080.graph fusedMap0512=true := by decide +kernel
theorem certified0512 : Certified (graph core0512) (root 10) 2 2 :=
  of_native_maps core0512 DegreeOneMiddleResidualSpectrum1370.graph DegreeTwoThreeSpectrum5080.graph
    sourceMap0512 fusedMap0512 sourceMap0512_checked fusedMap0512_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0512
#print axioms sourceMap0512_checked
#print axioms fusedMap0512_checked
#print axioms certified0512
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
