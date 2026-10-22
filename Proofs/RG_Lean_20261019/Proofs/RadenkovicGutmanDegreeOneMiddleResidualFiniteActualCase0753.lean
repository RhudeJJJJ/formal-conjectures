/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0753 : Family 10 := level10.get ⟨392,by decide⟩
def sourceMap0753 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0753 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0753_checked : acceptsGraphIso
    (source (graph core0753) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1879.graph sourceMap0753=true := by decide +kernel
theorem fusedMap0753_checked : acceptsGraphIso
    (fused (graph core0753) (root 10) 2 2) DegreeTwoThreeSpectrum5734.graph fusedMap0753=true := by decide +kernel
theorem certified0753 : Certified (graph core0753) (root 10) 2 2 :=
  of_native_maps core0753 DegreeOneMiddleResidualSpectrum1879.graph DegreeTwoThreeSpectrum5734.graph
    sourceMap0753 fusedMap0753 sourceMap0753_checked fusedMap0753_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0753
#print axioms sourceMap0753_checked
#print axioms fusedMap0753_checked
#print axioms certified0753
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
