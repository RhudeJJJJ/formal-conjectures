/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0845 : Family 10 := level10.get ⟨568,by decide⟩
def sourceMap0845 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0845 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0845_checked : acceptsGraphIso
    (source (graph core0845) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2058.graph sourceMap0845=true := by decide +kernel
theorem fusedMap0845_checked : acceptsGraphIso
    (fused (graph core0845) (root 10) 2 2) DegreeTwoThreeSpectrum5233.graph fusedMap0845=true := by decide +kernel
theorem certified0845 : Certified (graph core0845) (root 10) 2 2 :=
  of_native_maps core0845 DegreeOneMiddleResidualSpectrum2058.graph DegreeTwoThreeSpectrum5233.graph
    sourceMap0845 fusedMap0845 sourceMap0845_checked fusedMap0845_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0845
#print axioms sourceMap0845_checked
#print axioms fusedMap0845_checked
#print axioms certified0845
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
