/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0996 : Family 10 := level10.get ⟨879,by decide⟩
def sourceMap0996 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0996 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0996_checked : acceptsGraphIso
    (source (graph core0996) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2299.graph sourceMap0996=true := by decide +kernel
theorem fusedMap0996_checked : acceptsGraphIso
    (fused (graph core0996) (root 10) 2 2) DegreeTwoThreeSpectrum5729.graph fusedMap0996=true := by decide +kernel
theorem certified0996 : Certified (graph core0996) (root 10) 2 2 :=
  of_native_maps core0996 DegreeOneMiddleResidualSpectrum2299.graph DegreeTwoThreeSpectrum5729.graph
    sourceMap0996 fusedMap0996 sourceMap0996_checked fusedMap0996_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0996
#print axioms sourceMap0996_checked
#print axioms fusedMap0996_checked
#print axioms certified0996
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
