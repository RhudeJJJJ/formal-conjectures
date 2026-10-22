/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0428 : Family 9 := level9.get ⟨415,by decide⟩
def sourceMap0428 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0428 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0428_checked : acceptsGraphIso
    (source (graph core0428) (root 9) 2 2) DegreeOneMiddleResidualSpectrum816.graph sourceMap0428=true := by decide +kernel
theorem fusedMap0428_checked : acceptsGraphIso
    (fused (graph core0428) (root 9) 2 2) DegreeOneMiddleResidualSpectrum638.graph fusedMap0428=true := by decide +kernel
theorem certified0428 : Certified (graph core0428) (root 9) 2 2 :=
  of_native_maps core0428 DegreeOneMiddleResidualSpectrum816.graph DegreeOneMiddleResidualSpectrum638.graph
    sourceMap0428 fusedMap0428 sourceMap0428_checked fusedMap0428_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0428
#print axioms sourceMap0428_checked
#print axioms fusedMap0428_checked
#print axioms certified0428
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
