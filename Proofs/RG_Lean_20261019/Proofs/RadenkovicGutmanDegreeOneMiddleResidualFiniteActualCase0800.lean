/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0800 : Family 10 := level10.get ⟨480,by decide⟩
def sourceMap0800 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,8,9,10,11,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0800 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0800_checked : acceptsGraphIso
    (source (graph core0800) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1862.graph sourceMap0800=true := by decide +kernel
theorem fusedMap0800_checked : acceptsGraphIso
    (fused (graph core0800) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1506.graph fusedMap0800=true := by decide +kernel
theorem certified0800 : Certified (graph core0800) (root 10) 2 2 :=
  of_native_maps core0800 DegreeOneMiddleResidualSpectrum1862.graph DegreeOneMiddleResidualSpectrum1506.graph
    sourceMap0800 fusedMap0800 sourceMap0800_checked fusedMap0800_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0800
#print axioms sourceMap0800_checked
#print axioms fusedMap0800_checked
#print axioms certified0800
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
