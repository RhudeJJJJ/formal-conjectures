/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0115 : Family 8 := level8.get ⟨78,by decide⟩
def sourceMap0115 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap0115 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0115_checked : acceptsGraphIso
    (source (graph core0115) (root 8) 2 2) DegreeOneMiddleResidualSpectrum336.graph sourceMap0115=true := by decide +kernel
theorem fusedMap0115_checked : acceptsGraphIso
    (fused (graph core0115) (root 8) 2 2) DegreeTwoThreeSpectrum2394.graph fusedMap0115=true := by decide +kernel
theorem certified0115 : Certified (graph core0115) (root 8) 2 2 :=
  of_native_maps core0115 DegreeOneMiddleResidualSpectrum336.graph DegreeTwoThreeSpectrum2394.graph
    sourceMap0115 fusedMap0115 sourceMap0115_checked fusedMap0115_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0115
#print axioms sourceMap0115_checked
#print axioms fusedMap0115_checked
#print axioms certified0115
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
