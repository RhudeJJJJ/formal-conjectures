/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0896 : Family 10 := level10.get ⟨661,by decide⟩
def sourceMap0896 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap0896 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0896_checked : acceptsGraphIso
    (source (graph core0896) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2139.graph sourceMap0896=true := by decide +kernel
theorem fusedMap0896_checked : acceptsGraphIso
    (fused (graph core0896) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1214.graph fusedMap0896=true := by decide +kernel
theorem certified0896 : Certified (graph core0896) (root 10) 2 2 :=
  of_native_maps core0896 DegreeOneMiddleResidualSpectrum2139.graph DegreeOneMiddleResidualSpectrum1214.graph
    sourceMap0896 fusedMap0896 sourceMap0896_checked fusedMap0896_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0896
#print axioms sourceMap0896_checked
#print axioms fusedMap0896_checked
#print axioms certified0896
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
