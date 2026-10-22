/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0778 : Family 10 := level10.get ⟨436,by decide⟩
def sourceMap0778 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0778 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0778_checked : acceptsGraphIso
    (source (graph core0778) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1887.graph sourceMap0778=true := by decide +kernel
theorem fusedMap0778_checked : acceptsGraphIso
    (fused (graph core0778) (root 10) 2 2) DegreeTwoThreeSpectrum5847.graph fusedMap0778=true := by decide +kernel
theorem certified0778 : Certified (graph core0778) (root 10) 2 2 :=
  of_native_maps core0778 DegreeOneMiddleResidualSpectrum1887.graph DegreeTwoThreeSpectrum5847.graph
    sourceMap0778 fusedMap0778 sourceMap0778_checked fusedMap0778_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0778
#print axioms sourceMap0778_checked
#print axioms fusedMap0778_checked
#print axioms certified0778
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
