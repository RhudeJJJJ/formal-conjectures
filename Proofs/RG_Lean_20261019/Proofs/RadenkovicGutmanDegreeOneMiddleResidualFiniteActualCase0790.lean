/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0790 : Family 10 := level10.get ⟨457,by decide⟩
def sourceMap0790 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,8,9,10,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0790 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0790_checked : acceptsGraphIso
    (source (graph core0790) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1852.graph sourceMap0790=true := by decide +kernel
theorem fusedMap0790_checked : acceptsGraphIso
    (fused (graph core0790) (root 10) 2 2) DegreeTwoThreeSpectrum5893.graph fusedMap0790=true := by decide +kernel
theorem certified0790 : Certified (graph core0790) (root 10) 2 2 :=
  of_native_maps core0790 DegreeOneMiddleResidualSpectrum1852.graph DegreeTwoThreeSpectrum5893.graph
    sourceMap0790 fusedMap0790 sourceMap0790_checked fusedMap0790_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0790
#print axioms sourceMap0790_checked
#print axioms fusedMap0790_checked
#print axioms certified0790
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
