/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0412 : Family 9 := level9.get ⟨366,by decide⟩
def sourceMap0412 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0412 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0412_checked : acceptsGraphIso
    (source (graph core0412) (root 9) 2 2) DegreeOneMiddleResidualSpectrum780.graph sourceMap0412=true := by decide +kernel
theorem fusedMap0412_checked : acceptsGraphIso
    (fused (graph core0412) (root 9) 2 2) DegreeOneMiddleResidualSpectrum602.graph fusedMap0412=true := by decide +kernel
theorem certified0412 : Certified (graph core0412) (root 9) 2 2 :=
  of_native_maps core0412 DegreeOneMiddleResidualSpectrum780.graph DegreeOneMiddleResidualSpectrum602.graph
    sourceMap0412 fusedMap0412 sourceMap0412_checked fusedMap0412_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0412
#print axioms sourceMap0412_checked
#print axioms fusedMap0412_checked
#print axioms certified0412
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
