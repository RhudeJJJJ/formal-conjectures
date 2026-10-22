/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0755 : Family 10 := level10.get ⟨395,by decide⟩
def sourceMap0755 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0755 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0755_checked : acceptsGraphIso
    (source (graph core0755) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1912.graph sourceMap0755=true := by decide +kernel
theorem fusedMap0755_checked : acceptsGraphIso
    (fused (graph core0755) (root 10) 2 2) DegreeTwoThreeSpectrum5743.graph fusedMap0755=true := by decide +kernel
theorem certified0755 : Certified (graph core0755) (root 10) 2 2 :=
  of_native_maps core0755 DegreeOneMiddleResidualSpectrum1912.graph DegreeTwoThreeSpectrum5743.graph
    sourceMap0755 fusedMap0755 sourceMap0755_checked fusedMap0755_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0755
#print axioms sourceMap0755_checked
#print axioms fusedMap0755_checked
#print axioms certified0755
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
