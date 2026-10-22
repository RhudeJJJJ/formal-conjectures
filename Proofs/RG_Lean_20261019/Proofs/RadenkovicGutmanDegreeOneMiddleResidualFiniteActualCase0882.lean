/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0882 : Family 10 := level10.get ⟨633,by decide⟩
def sourceMap0882 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0882 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0882_checked : acceptsGraphIso
    (source (graph core0882) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2125.graph sourceMap0882=true := by decide +kernel
theorem fusedMap0882_checked : acceptsGraphIso
    (fused (graph core0882) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1189.graph fusedMap0882=true := by decide +kernel
theorem certified0882 : Certified (graph core0882) (root 10) 2 2 :=
  of_native_maps core0882 DegreeOneMiddleResidualSpectrum2125.graph DegreeOneMiddleResidualSpectrum1189.graph
    sourceMap0882 fusedMap0882 sourceMap0882_checked fusedMap0882_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0882
#print axioms sourceMap0882_checked
#print axioms fusedMap0882_checked
#print axioms certified0882
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
