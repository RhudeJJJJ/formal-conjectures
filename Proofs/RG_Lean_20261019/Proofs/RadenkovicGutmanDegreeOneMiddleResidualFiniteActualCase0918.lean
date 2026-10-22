/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0918 : Family 10 := level10.get ⟨713,by decide⟩
def sourceMap0918 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0918 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0918_checked : acceptsGraphIso
    (source (graph core0918) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2181.graph sourceMap0918=true := by decide +kernel
theorem fusedMap0918_checked : acceptsGraphIso
    (fused (graph core0918) (root 10) 2 2) DegreeTwoThreeSpectrum5459.graph fusedMap0918=true := by decide +kernel
theorem certified0918 : Certified (graph core0918) (root 10) 2 2 :=
  of_native_maps core0918 DegreeOneMiddleResidualSpectrum2181.graph DegreeTwoThreeSpectrum5459.graph
    sourceMap0918 fusedMap0918 sourceMap0918_checked fusedMap0918_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0918
#print axioms sourceMap0918_checked
#print axioms fusedMap0918_checked
#print axioms certified0918
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
