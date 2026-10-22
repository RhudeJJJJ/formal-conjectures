/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0964 : Family 10 := level10.get ⟨803,by decide⟩
def sourceMap0964 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap0964 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0964_checked : acceptsGraphIso
    (source (graph core0964) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2252.graph sourceMap0964=true := by decide +kernel
theorem fusedMap0964_checked : acceptsGraphIso
    (fused (graph core0964) (root 10) 2 2) DegreeTwoThreeSpectrum5599.graph fusedMap0964=true := by decide +kernel
theorem certified0964 : Certified (graph core0964) (root 10) 2 2 :=
  of_native_maps core0964 DegreeOneMiddleResidualSpectrum2252.graph DegreeTwoThreeSpectrum5599.graph
    sourceMap0964 fusedMap0964 sourceMap0964_checked fusedMap0964_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0964
#print axioms sourceMap0964_checked
#print axioms fusedMap0964_checked
#print axioms certified0964
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
